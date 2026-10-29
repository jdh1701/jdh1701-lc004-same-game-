"""Claim registry with lineage (why_believe / what_depends_on)."""
CLAIMS = {
 "C0": ("Certificate theorem: win <=> NC refinement into 2/3-blocks", [], "external: Biedl et al. 2002 Thm 2; LC004 raw_max_win_iff_certificate (Lean)"),
 "C1": ("Rigidity: classes of size 2 or 3 are blocks of every certificate", ["C0"], "elementary"),
 "C2": ("Face lemma: win <=> rigid skeleton NC and every face word wins", ["C0", "C1"], "proof Step 2"),
 "C3": ("Slot bijection: face word + cut points <-> placements", [], "proof Step 3"),
 "C4": ("Goulden-Jackson type/cotype count of NC partitions", [], "external: GJ 1992; Krattenthaler-Muller Thm 5"),
 "C5": ("Rotation averaging: outer face has weight d/N0", [], "proof Step 4"),
 "C6": ("Generating-function simplification (D-trick, substitution)", [], "proof Step 5"),
 "T":  ("Face decomposition counting theorem", ["C2", "C3", "C4", "C5", "C6"], "proof"),
 "K1": ("Kreweras recovered for pairs/triples", ["T"], "corollary"),
 "K2": ("One heavy class: ratio c_s(b)/b", ["T"], "corollary"),
 "K3": ("Second diagonal A(2k+2,k)=k C(2k+2,k-1); htriple; hfour", ["T", "LC004:W4=R-D", "LC004:2R=(k+3)B"], "corollary"),
 "K4": ("Closed forms of A(2k+j,k), j<=7", ["T"], "corollary + degree bound + 40-point match"),
 "K5": ("Involution leading-term law, all j", ["T"], "corollary 5 proof"),
 "D1": ("A(n,2) closed form", ["external:Burns-Purcell"], "published"),
 "D2": ("A(n,3) for n<=25", ["D1", "external:A035617"], "derived from published data"),
 "N1": ("No prior source for T, K2, K4, K5", [], "literature search (OEIS search blocked)"),
 "N2": ("Column 3 has no small P-recursive or algebraic GF", ["D2"], "linear algebra on 26 terms"),
}

def what_depends_on(cid):
    return [k for k, (_, deps, _) in CLAIMS.items() if cid in deps]

def why_believe(cid):
    s, deps, basis = CLAIMS[cid]
    return {"claim": s, "basis": basis, "depends": deps}

if __name__ == "__main__":
    for k in CLAIMS:
        print(k, "<-", CLAIMS[k][1], "| supports:", what_depends_on(k))
