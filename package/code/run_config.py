"""
run_config.py — the single configuration object for one run of the Galois-group
artifact, and the writer that records it in the run directory at the start of
every run.

Fields correspond to the derivations in the accompanying paper:

  coefficient_ring     the three approximation rings   case 1 Z, case 2 O_K, case 3 F_q[t]
  polynomial           the input conventions     monic separable f in R[x], coefficients as strings
  approximation        the three approximation rings   prime p (with residue degree s), local datum
                              (uniformizer, tower, e'), or place t0 (with s)
  precision_policy     recognition and proof precisions     how k is chosen and escalated: k_rec, k_prf, k_id,
                              effective-precision accounting (effective precision after Hensel lifting), hard cap
  invariant_table_path ring-independent invariants     table of (U,V) -> invariant in normal form
  pruning_sources      coset pruning by a certified element   which certified elements / class data may prune
  terminal_preference  the certificate format   T1 / T2 / T3 order of preference
  family_check         the validation families    which of the three family checks to run, if any

Every value is plain data (JSON-serialisable). No computation happens here; the
checker recomputes everything it needs from witnesses, so this object is a
record of *choices*, not of claims.
"""

from __future__ import annotations

import dataclasses
import datetime as _dt
import hashlib
import json
import os
import secrets
from dataclasses import dataclass, field
from typing import Any, Dict, List, Literal, Optional


# ----------------------------------------------------------------------------
# Coefficient ring (the three approximation rings)
# ----------------------------------------------------------------------------

RingKind = Literal["Z", "O_K", "Fq[t]"]


@dataclass(frozen=True)
class CoefficientRing:
    kind: RingKind
    # case 2: K given by p and a defining polynomial over Q_p (string, in 'y'),
    #         with the residue degree and ramification index of K/Q_p
    p: Optional[int] = None
    K_defining_poly: Optional[str] = None
    K_residue_degree: Optional[int] = None
    K_ramification_index: Optional[int] = None
    # case 3: q = p^a and the defining polynomial of F_q over F_p (string, in 'z')
    q: Optional[int] = None
    Fq_defining_poly: Optional[str] = None

    def validate(self) -> None:
        if self.kind == "Z":
            return
        if self.kind == "O_K":
            if self.p is None or self.K_defining_poly is None:
                raise ValueError("O_K requires p and K_defining_poly")
            if self.K_ramification_index is None or self.K_residue_degree is None:
                raise ValueError("O_K requires K_ramification_index and K_residue_degree")
            return
        if self.kind == "Fq[t]":
            if self.q is None:
                raise ValueError("Fq[t] requires q")
            if self.q > 1 and not _is_prime_power(self.q):
                raise ValueError("q must be a prime power")
            if self.q != _smallest_prime_factor(self.q) and self.Fq_defining_poly is None:
                raise ValueError("non-prime q requires Fq_defining_poly")
            return
        raise ValueError(f"unknown ring kind {self.kind!r}")

    @property
    def case(self) -> int:
        return {"Z": 1, "O_K": 2, "Fq[t]": 3}[self.kind]


# ----------------------------------------------------------------------------
# Polynomial (the input conventions): monic, coefficients a_0..a_{n-1} as strings in the ring
# ----------------------------------------------------------------------------

@dataclass(frozen=True)
class Polynomial:
    degree: int
    coefficients: List[str]          # a_0, ..., a_{n-1}; leading coefficient is 1
    variable: str = "x"
    # case 3 only: the t-degree bound delta used in B (the three approximation rings); recomputed by the
    # checker, recorded here so the prover's and checker's delta can be compared
    coefficient_size_hint: Optional[str] = None

    def validate(self, ring: CoefficientRing) -> None:
        if self.degree < 1:
            raise ValueError("degree must be >= 1")
        if len(self.coefficients) != self.degree:
            raise ValueError("need exactly degree coefficients a_0..a_{n-1} (monic)")
        if ring.kind == "Z":
            for c in self.coefficients:
                int(c)  # must parse as an integer
        # For O_K and Fq[t] the coefficient strings are parsed by the ring
        # backend; here we only check they are non-empty.
        for c in self.coefficients:
            if not isinstance(c, str) or not c.strip():
                raise ValueError("coefficients must be non-empty strings")


# ----------------------------------------------------------------------------
# Approximation datum (the three approximation rings, effective precision after Hensel lifting, certified Frobenius and inertia elements)
# ----------------------------------------------------------------------------

@dataclass(frozen=True)
class ApproximationDatum:
    kind: Literal["prime", "local", "place"]
    # case 1: prime p with p ∤ disc f; s = lcm of factor degrees of f mod p,
    #         so roots live in O_q, q = p^s. require_degree_one_root: choice of a degree-one prime.
    p: Optional[int] = None
    residue_degree_s: Optional[int] = None
    require_degree_one_root: bool = False
    # case 2: K'/K given as a tower of (unramified step, then Eisenstein steps),
    #         each step a polynomial string over the previous field; e' and the
    #         input precision N of the tower / of f (size bounds for resolvent values, disc ≢ 0 mod π^N).
    tower: Optional[List[Dict[str, Any]]] = None
    ramification_index_e_prime: Optional[int] = None
    input_precision_N: Optional[int] = None
    # case 3: place t0 (element of F_{q^{s0}} as a string) with disc f(t0) ≠ 0;
    #         s = lcm of factor degrees of f(t0, x); roots in F_{q^s}[[t - t0]].
    t0: Optional[str] = None
    t0_constant_extension_degree: int = 1
    constant_extension_s: Optional[int] = None

    def validate(self, ring: CoefficientRing) -> None:
        expected = {1: "prime", 2: "local", 3: "place"}[ring.case]
        if self.kind != expected:
            raise ValueError(f"ring case {ring.case} requires approximation kind {expected!r}")
        if self.kind == "prime":
            if self.p is None or self.p < 2 or not _is_prime(self.p):
                raise ValueError("prime datum requires a prime p")
            if self.residue_degree_s is None or self.residue_degree_s < 1:
                raise ValueError("prime datum requires residue_degree_s >= 1")
        elif self.kind == "local":
            if not self.tower:
                raise ValueError("local datum requires a non-empty tower")
            if self.ramification_index_e_prime is None or self.ramification_index_e_prime < 1:
                raise ValueError("local datum requires ramification_index_e_prime")
            if self.input_precision_N is None or self.input_precision_N < 1:
                raise ValueError("local datum requires input_precision_N")
        else:
            if self.t0 is None:
                raise ValueError("place datum requires t0")
            if self.constant_extension_s is None or self.constant_extension_s < 1:
                raise ValueError("place datum requires constant_extension_s >= 1")


# ----------------------------------------------------------------------------
# Precision policy (recognition and proof precisions, effective precision after Hensel lifting)
# ----------------------------------------------------------------------------

@dataclass(frozen=True)
class PrecisionPolicy:
    # Starting precision for a Stauduhar step: 'k_rec' (recognition only, then
    # escalate to k_prf for the coset that passed), 'k_prf' (prove directly), or
    # 'fixed' (use fixed_k for every step; rejected by the checker if too small).
    initial: Literal["k_rec", "k_prf", "fixed"] = "k_rec"
    fixed_k: Optional[int] = None
    # Escalation when a step needs more precision: 'to_k_prf' jumps to the
    # recomputed k_prf(N, B) (and k_id); 'double' doubles until the checks pass.
    escalation: Literal["to_k_prf", "double"] = "to_k_prf"
    # Hard cap on the precision of the root approximations (k_max in the certificate format).
    max_precision: int = 1 << 20
    # effective precision after Hensel lifting: subtract v(f'(α̃)) (and tower losses) from k before any comparison.
    effective_precision_accounting: bool = True
    # size bounds for resolvent values: local case decisions by pairwise separation + image check. The
    # alternative 'newton_polygon' is the from-R-alone method of root verification over a local field.
    local_certificate: Literal["pairwise_separation", "newton_polygon"] = "pairwise_separation"
    # the checker conditions C0-C6: Tschirnhaus sample set size factor relative to N(N-1)d.
    tschirnhaus_sample_factor: int = 2

    def validate(self) -> None:
        if self.initial == "fixed" and (self.fixed_k is None or self.fixed_k < 1):
            raise ValueError("fixed precision policy requires fixed_k >= 1")
        if self.max_precision < 1:
            raise ValueError("max_precision must be >= 1")
        if self.tschirnhaus_sample_factor < 2:
            raise ValueError("tschirnhaus_sample_factor must be >= 2 (Schwartz–Zippel)")


# ----------------------------------------------------------------------------
# Pruning sources (certified group elements) and terminal certificate preference (the certificate format)
# ----------------------------------------------------------------------------

PruningSource = Literal[
    "frobenius_local",        # certified Frobenius and inertia elements: τ at the approximation prime/place, coset filter
    "frobenius_other_primes", # coset pruning by a certified element: cycle types at other primes, pair filter
    "inertia_tame",           # certified Frobenius and inertia elements: ι of a tame K'/K, coset filter (case 2)
    "ramification_constraints",  # certified Frobenius and inertia elements wild case: |I|, tame/wild split, pair filter
    "block_structure",        # the three invariant constructions/subfields and the starting group: Type I/II restriction of maximal pairs
    "constant_field_divisibility",  # the constant-field theory over F_q(t): c | gcd ord(Frob_{t1}), case 3 geometric steps
]

TerminalKind = Literal["T1", "T2", "T3"]


# ----------------------------------------------------------------------------
# Family check selection (the validation families)
# ----------------------------------------------------------------------------

@dataclass(frozen=True)
class FamilyCheck:
    family: Optional[Literal["composition", "eisenstein", "sparse_specialization"]] = None
    # composition: g, h as coefficient lists, the proven Gal(g) and the proven
    #   relative group Gal(h(x)-β / Q(β)) as permutation-group generator lists,
    #   and the proven group of f if available.
    # eisenstein: nothing extra (splitting field is the approximation datum).
    # sparse_specialization: W_cl, A_cl generators, block structure, and the
    #   classification's "full group" conditions as a predicate name.
    data: Dict[str, Any] = field(default_factory=dict)

    def validate(self) -> None:
        if self.family is None:
            return
        need = {
            "composition": {"g", "h", "gal_g", "relative_gal_h"},
            "eisenstein": set(),
            "sparse_specialization": {"W_cl", "A_cl", "block_structure"},
        }[self.family]
        missing = need - set(self.data)
        if missing:
            raise ValueError(f"family check {self.family!r} missing data {sorted(missing)}")


# ----------------------------------------------------------------------------
# The configuration object
# ----------------------------------------------------------------------------

DERIVATION_VERSION = "galois-certificate-derivations@final"


@dataclass(frozen=True)
class RunConfig:
    coefficient_ring: CoefficientRing
    polynomial: Polynomial
    approximation: ApproximationDatum
    precision_policy: PrecisionPolicy
    invariant_table_path: str
    pruning_sources: List[PruningSource]
    terminal_preference: List[TerminalKind] = field(default_factory=lambda: ["T1", "T2", "T3"])
    family_check: FamilyCheck = field(default_factory=FamilyCheck)
    # bookkeeping
    run_id: str = field(default_factory=lambda: _dt.datetime.now(_dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + secrets.token_hex(4))
    created_utc: str = field(default_factory=lambda: _dt.datetime.now(_dt.timezone.utc).isoformat())
    derivation_version: str = DERIVATION_VERSION
    notes: str = ""

    # ---- validation ------------------------------------------------------

    def validate(self) -> None:
        self.coefficient_ring.validate()
        self.polynomial.validate(self.coefficient_ring)
        self.approximation.validate(self.coefficient_ring)
        self.precision_policy.validate()
        self.family_check.validate()
        if not self.invariant_table_path:
            raise ValueError("invariant_table_path must be set")
        allowed = set(PruningSource.__args__)  # type: ignore[attr-defined]
        bad = [s for s in self.pruning_sources if s not in allowed]
        if bad:
            raise ValueError(f"unknown pruning sources {bad}")
        if len(set(self.pruning_sources)) != len(self.pruning_sources):
            raise ValueError("duplicate pruning sources")
        # case-specific admissibility of pruning sources (certified Frobenius and inertia elements)
        case = self.coefficient_ring.case
        if "inertia_tame" in self.pruning_sources and case != 2:
            raise ValueError("inertia_tame pruning is only available in case 2")
        if "constant_field_divisibility" in self.pruning_sources and case != 3:
            raise ValueError("constant_field_divisibility pruning is only available in case 3")
        if "frobenius_local" in self.pruning_sources and case == 2:
            # certified Frobenius and inertia elements: only a coset of the Frobenius is available in case 2
            raise ValueError("frobenius_local coset pruning is not available in case 2 (only a coset τ̃·I is known)")
        if "T2" in self.terminal_preference and case == 2:
            raise ValueError("T2 (Galois-resolvent irreducibility) is restricted to cases 1 and 3")
        if self.family_check.family == "composition" and case != 1:
            raise ValueError("composition family check applies to case 1")
        if self.family_check.family == "eisenstein" and case != 2:
            raise ValueError("eisenstein family check applies to case 2")
        if self.family_check.family == "sparse_specialization" and case != 3:
            raise ValueError("sparse_specialization family check applies to case 3")
        if self.precision_policy.local_certificate == "newton_polygon" and case != 2:
            raise ValueError("newton_polygon local certificate applies to case 2 only")

    # ---- serialisation ---------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        return dataclasses.asdict(self)

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), indent=2, sort_keys=True)

    def content_hash(self) -> str:
        """Hash of the configuration *excluding* run_id / created_utc, so that
        two runs with identical choices have identical hashes."""
        d = self.to_dict()
        d.pop("run_id", None)
        d.pop("created_utc", None)
        blob = json.dumps(d, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(blob).hexdigest()

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> "RunConfig":
        return RunConfig(
            coefficient_ring=CoefficientRing(**d["coefficient_ring"]),
            polynomial=Polynomial(**d["polynomial"]),
            approximation=ApproximationDatum(**d["approximation"]),
            precision_policy=PrecisionPolicy(**d["precision_policy"]),
            invariant_table_path=d["invariant_table_path"],
            pruning_sources=list(d["pruning_sources"]),
            terminal_preference=list(d.get("terminal_preference", ["T1", "T2", "T3"])),
            family_check=FamilyCheck(**d.get("family_check", {})),
            run_id=d.get("run_id", ""),
            created_utc=d.get("created_utc", ""),
            derivation_version=d.get("derivation_version",
                                      d.get("spec_version", DERIVATION_VERSION)),
            notes=d.get("notes", ""),
        )


# ----------------------------------------------------------------------------
# Writing the configuration at the start of every run
# ----------------------------------------------------------------------------

CONFIG_FILENAME = "config.json"
HISTORY_DIRNAME = "config_history"


def write_run_config(config: RunConfig, run_dir: str) -> str:
    """Validate `config`, then write it to `<run_dir>/config.json` atomically and
    append an immutable copy to `<run_dir>/config_history/<run_id>.json`.
    Returns the path of config.json. Called by `start_run`; must be the first
    action of a run so that every later artifact can be tied to these choices."""
    config.validate()
    os.makedirs(run_dir, exist_ok=True)
    hist = os.path.join(run_dir, HISTORY_DIRNAME)
    os.makedirs(hist, exist_ok=True)

    payload = config.to_json() + "\n"

    # history copy: never overwritten (run_id is unique per run)
    hist_path = os.path.join(hist, f"{config.run_id}.json")
    if os.path.exists(hist_path):
        raise FileExistsError(f"run_id collision: {hist_path}")
    _atomic_write(hist_path, payload)

    # current copy: replaced atomically
    cur_path = os.path.join(run_dir, CONFIG_FILENAME)
    _atomic_write(cur_path, payload)

    # a tiny marker with the content hash, convenient for the checker to verify
    # that the certificate it is reading was produced under this configuration
    _atomic_write(os.path.join(run_dir, "config.sha256"), config.content_hash() + "\n")
    return cur_path


def read_run_config(run_dir: str) -> RunConfig:
    with open(os.path.join(run_dir, CONFIG_FILENAME)) as fh:
        cfg = RunConfig.from_dict(json.load(fh))
    cfg.validate()
    return cfg


def start_run(config: RunConfig, run_dir: str):
    """Entry point for a run: record the configuration first, then return a
    context the prover/checker can use. Everything else (root approximation,
    lattice, descent, certificate, checker) is invoked after this returns."""
    path = write_run_config(config, run_dir)
    return {
        "run_dir": run_dir,
        "config_path": path,
        "config_hash": config.content_hash(),
        "run_id": config.run_id,
        "case": config.coefficient_ring.case,
    }


# ----------------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------------

def _atomic_write(path: str, text: str) -> None:
    tmp = f"{path}.tmp.{secrets.token_hex(3)}"
    with open(tmp, "w") as fh:
        fh.write(text)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def _is_prime(m: int) -> bool:
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0:
            return False
        i += 2
    return True


def _smallest_prime_factor(m: int) -> int:
    if m % 2 == 0:
        return 2
    i = 3
    while i * i <= m:
        if m % i == 0:
            return i
        i += 2
    return m


def _is_prime_power(m: int) -> bool:
    if m < 2:
        return False
    p = _smallest_prime_factor(m)
    while m % p == 0:
        m //= p
    return m == 1


# ----------------------------------------------------------------------------
# example configurations, one per case
# ----------------------------------------------------------------------------

def example_case1() -> RunConfig:
    # f = (x^3 - x)^2 - 2 = x^6 - 2x^4 + x^2 - 2   (the the validation families Check-1 example)
    return RunConfig(
        coefficient_ring=CoefficientRing(kind="Z"),
        polynomial=Polynomial(degree=6, coefficients=["-2", "0", "1", "0", "-2", "0"]),
        approximation=ApproximationDatum(kind="prime", p=7, residue_degree_s=3, require_degree_one_root=True),
        precision_policy=PrecisionPolicy(initial="k_rec", escalation="to_k_prf"),
        invariant_table_path="tables/invariants_n6.json",
        pruning_sources=["frobenius_local", "frobenius_other_primes", "block_structure"],
        terminal_preference=["T1", "T2", "T3"],
        family_check=FamilyCheck(
            family="composition",
            data={"g": ["-2", "0"], "h": ["0", "-1", "0"], "gal_g": [[1, 0]], "relative_gal_h": [[1, 2, 0], [1, 0, 2]]},
        ),
        notes="composition g∘h with g=x^2-2, h=x^3-x; relative block group S_3, Gal(h) trivial",
    )


def example_case2() -> RunConfig:
    # Eisenstein x^3 - 5 over Q_5 (K = Q_5), tame: K' = Q_25(α), e' = 3, the tower used by hensel_frobenius.case2
    return RunConfig(
        coefficient_ring=CoefficientRing(kind="O_K", p=5, K_defining_poly="y", K_residue_degree=1, K_ramification_index=1),
        polynomial=Polynomial(degree=3, coefficients=["-5", "0", "0"]),
        approximation=ApproximationDatum(
            kind="local",
            tower=[{"kind": "unramified", "poly": "z^2+2"}, {"kind": "eisenstein", "poly": "w^3-5"}],
            ramification_index_e_prime=3,
            input_precision_N=64,
        ),
        precision_policy=PrecisionPolicy(initial="k_prf", escalation="double", local_certificate="pairwise_separation"),
        invariant_table_path="tables/invariants_n3.json",
        pruning_sources=["inertia_tame", "block_structure"],
        terminal_preference=["T1", "T3"],
        family_check=FamilyCheck(family="eisenstein"),
        notes="tame Eisenstein: inertia generator and canonical Frobenius lift generate S_3 (T1)",
    )


def example_case3() -> RunConfig:
    # sparse specialization over F_3(t): x^5 + t x + 1
    return RunConfig(
        coefficient_ring=CoefficientRing(kind="Fq[t]", q=3),
        polynomial=Polynomial(degree=5, coefficients=["1", "t", "0", "0", "0"]),
        approximation=ApproximationDatum(kind="place", t0="1", constant_extension_s=4),
        precision_policy=PrecisionPolicy(initial="k_rec", escalation="to_k_prf"),
        invariant_table_path="tables/invariants_n5.json",
        pruning_sources=["frobenius_local", "frobenius_other_primes", "block_structure", "constant_field_divisibility"],
        terminal_preference=["T2", "T3", "T1"],
        family_check=FamilyCheck(
            family="sparse_specialization",
            data={"W_cl": "S5", "A_cl": "S5", "block_structure": [[0, 1, 2, 3, 4]], "full_group_predicate": "trinomial_generic"},
        ),
        notes="trinomial x^5 + t x + 1; geometric group compared with the lacunary classification",
    )


if __name__ == "__main__":
    import sys
    run_dir = sys.argv[1] if len(sys.argv) > 1 else "runs/example"
    for cfg in (example_case1(), example_case2(), example_case3()):
        ctx = start_run(cfg, os.path.join(run_dir, f"case{cfg.coefficient_ring.case}"))
        print(json.dumps(ctx, indent=2))