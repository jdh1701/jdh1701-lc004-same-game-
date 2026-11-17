import AlexandriaComplexity.SetResolution

namespace AlexandriaComplexity

/-!
Generated from the frozen odd-charge cubic-family receipt.
This exact finite certificate is not an asymptotic lower bound and
has no P-versus-NP consequence.
-/

private abbrev p (index : Nat) : Literal := positiveLiteral index
private abbrev n (index : Nat) : Literal := negativeLiteral index

def triangularPrismFamilyJsonSHA256 : String :=
  "917818f914d2e614ebb7c7b6c56214cc394172f09cc0527fe01b1135f7946da2"

def triangularPrismFormulaSHA256 : String :=
  "52d906e906f4d32babd87ff0b642c7683dd5e1a01db3a30d05b4f4be5feaec78"

def triangularPrismOddTseitinCNF : CNF := [
  [p 0, p 1, p 2],
  [p 0, n 1, n 2],
  [n 0, p 1, n 2],
  [n 0, n 1, p 2],
  [p 0, p 3, n 4],
  [p 0, n 3, p 4],
  [n 0, p 3, p 4],
  [n 0, n 3, n 4],
  [p 1, p 3, n 5],
  [p 1, n 3, p 5],
  [n 1, p 3, p 5],
  [n 1, n 3, n 5],
  [p 2, p 6, n 7],
  [p 2, n 6, p 7],
  [n 2, p 6, p 7],
  [n 2, n 6, n 7],
  [p 4, p 6, n 8],
  [p 4, n 6, p 8],
  [n 4, p 6, p 8],
  [n 4, n 6, n 8],
  [p 5, p 7, n 8],
  [p 5, n 7, p 8],
  [n 5, p 7, p 8],
  [n 5, n 7, n 8]
]

theorem triangular_prism_set_resolution_certificate :
    SetResolutionDerivation triangularPrismOddTseitinCNF [] := by
  let c0 : Clause := [p 5, p 7, n 8]
  let c1 : Clause := [n 4, n 6, n 8]
  let c2 : Clause := [p 2, p 6, n 7]
  let c3 : Clause := [p 2, n 4, n 7, n 8]
  let c4 : Clause := [p 2, n 4, p 5, n 8]
  let c5 : Clause := [p 5, n 7, p 8]
  let c6 : Clause := [n 4, p 6, p 8]
  let c7 : Clause := [p 2, n 6, p 7]
  let c8 : Clause := [p 2, n 4, p 7, p 8]
  let c9 : Clause := [p 2, n 4, p 5, p 8]
  let c10 : Clause := [p 2, n 4, p 5]
  let c11 : Clause := [n 0, n 1, p 2]
  let c12 : Clause := [n 1, n 3, n 5]
  let c13 : Clause := [p 0, p 3, n 4]
  let c14 : Clause := [p 0, n 1, n 4, n 5]
  let c15 : Clause := [n 1, p 2, n 4, n 5]
  let c16 : Clause := [p 1, p 3, n 5]
  let c17 : Clause := [n 0, n 3, n 4]
  let c18 : Clause := [p 0, p 1, p 2]
  let c19 : Clause := [p 1, p 2, n 3, n 4]
  let c20 : Clause := [p 1, p 2, n 4, n 5]
  let c21 : Clause := [p 2, n 4, n 5]
  let c22 : Clause := [p 2, n 4]
  let c23 : Clause := [p 4, p 6, n 8]
  let c24 : Clause := [n 5, n 7, n 8]
  let c25 : Clause := [p 2, n 5, n 6, n 8]
  let c26 : Clause := [p 2, p 4, n 5, n 8]
  let c27 : Clause := [p 4, n 6, p 8]
  let c28 : Clause := [n 5, p 7, p 8]
  let c29 : Clause := [p 2, n 5, p 6, p 8]
  let c30 : Clause := [p 2, p 4, n 5, p 8]
  let c31 : Clause := [p 2, p 4, n 5]
  let c32 : Clause := [n 0, p 3, p 4]
  let c33 : Clause := [n 1, p 3, p 5]
  let c34 : Clause := [p 0, p 2, p 3, p 5]
  let c35 : Clause := [p 2, p 3, p 4, p 5]
  let c36 : Clause := [p 1, n 3, p 5]
  let c37 : Clause := [p 0, n 3, p 4]
  let c38 : Clause := [n 1, p 2, n 3, p 4]
  let c39 : Clause := [p 2, n 3, p 4, p 5]
  let c40 : Clause := [p 2, p 4, p 5]
  let c41 : Clause := [p 2, p 4]
  let c42 : Clause := [p 2]
  let c43 : Clause := [n 2, n 6, n 7]
  let c44 : Clause := [n 2, p 4, n 7, n 8]
  let c45 : Clause := [n 2, p 4, p 5, n 8]
  let c46 : Clause := [n 2, p 6, p 7]
  let c47 : Clause := [n 2, p 4, p 7, p 8]
  let c48 : Clause := [n 2, p 4, p 5, p 8]
  let c49 : Clause := [n 2, p 4, p 5]
  let c50 : Clause := [n 0, p 1, n 2]
  let c51 : Clause := [n 0, n 2, p 3, p 5]
  let c52 : Clause := [n 2, p 3, n 4, p 5]
  let c53 : Clause := [p 0, n 1, n 2]
  let c54 : Clause := [n 1, n 2, n 3, n 4]
  let c55 : Clause := [n 2, n 3, n 4, p 5]
  let c56 : Clause := [n 2, n 4, p 5]
  let c57 : Clause := [n 2, p 5]
  let c58 : Clause := [n 4, n 5, p 6, n 7]
  let c59 : Clause := [n 2, n 4, n 5, p 6]
  let c60 : Clause := [n 4, n 5, n 6, p 7]
  let c61 : Clause := [n 2, n 4, n 5, n 6]
  let c62 : Clause := [n 2, n 4, n 5]
  let c63 : Clause := [n 0, n 1, p 4, n 5]
  let c64 : Clause := [n 1, n 2, p 4, n 5]
  let c65 : Clause := [p 1, n 2, n 3, p 4]
  let c66 : Clause := [p 1, n 2, p 4, n 5]
  let c67 : Clause := [n 2, p 4, n 5]
  let c68 : Clause := [n 2, n 5]
  let c69 : Clause := [n 2]
  let c70 : Clause := []

  have d0 : SetResolutionDerivation triangularPrismOddTseitinCNF c0 :=
    .initial c0 (by decide)
  have d1 : SetResolutionDerivation triangularPrismOddTseitinCNF c1 :=
    .initial c1 (by decide)
  have d2 : SetResolutionDerivation triangularPrismOddTseitinCNF c2 :=
    .initial c2 (by decide)
  have d3 : SetResolutionDerivation triangularPrismOddTseitinCNF c3 :=
    .resolve 6 c2 c1 c3
      (by decide) (by decide) (by decide) d2 d1
  have d4 : SetResolutionDerivation triangularPrismOddTseitinCNF c4 :=
    .resolve 7 c0 c3 c4
      (by decide) (by decide) (by decide) d0 d3
  have d5 : SetResolutionDerivation triangularPrismOddTseitinCNF c5 :=
    .initial c5 (by decide)
  have d6 : SetResolutionDerivation triangularPrismOddTseitinCNF c6 :=
    .initial c6 (by decide)
  have d7 : SetResolutionDerivation triangularPrismOddTseitinCNF c7 :=
    .initial c7 (by decide)
  have d8 : SetResolutionDerivation triangularPrismOddTseitinCNF c8 :=
    .resolve 6 c6 c7 c8
      (by decide) (by decide) (by decide) d6 d7
  have d9 : SetResolutionDerivation triangularPrismOddTseitinCNF c9 :=
    .resolve 7 c8 c5 c9
      (by decide) (by decide) (by decide) d8 d5
  have d10 : SetResolutionDerivation triangularPrismOddTseitinCNF c10 :=
    .resolve 8 c9 c4 c10
      (by decide) (by decide) (by decide) d9 d4
  have d11 : SetResolutionDerivation triangularPrismOddTseitinCNF c11 :=
    .initial c11 (by decide)
  have d12 : SetResolutionDerivation triangularPrismOddTseitinCNF c12 :=
    .initial c12 (by decide)
  have d13 : SetResolutionDerivation triangularPrismOddTseitinCNF c13 :=
    .initial c13 (by decide)
  have d14 : SetResolutionDerivation triangularPrismOddTseitinCNF c14 :=
    .resolve 3 c13 c12 c14
      (by decide) (by decide) (by decide) d13 d12
  have d15 : SetResolutionDerivation triangularPrismOddTseitinCNF c15 :=
    .resolve 0 c14 c11 c15
      (by decide) (by decide) (by decide) d14 d11
  have d16 : SetResolutionDerivation triangularPrismOddTseitinCNF c16 :=
    .initial c16 (by decide)
  have d17 : SetResolutionDerivation triangularPrismOddTseitinCNF c17 :=
    .initial c17 (by decide)
  have d18 : SetResolutionDerivation triangularPrismOddTseitinCNF c18 :=
    .initial c18 (by decide)
  have d19 : SetResolutionDerivation triangularPrismOddTseitinCNF c19 :=
    .resolve 0 c18 c17 c19
      (by decide) (by decide) (by decide) d18 d17
  have d20 : SetResolutionDerivation triangularPrismOddTseitinCNF c20 :=
    .resolve 3 c16 c19 c20
      (by decide) (by decide) (by decide) d16 d19
  have d21 : SetResolutionDerivation triangularPrismOddTseitinCNF c21 :=
    .resolve 1 c20 c15 c21
      (by decide) (by decide) (by decide) d20 d15
  have d22 : SetResolutionDerivation triangularPrismOddTseitinCNF c22 :=
    .resolve 5 c10 c21 c22
      (by decide) (by decide) (by decide) d10 d21
  have d23 : SetResolutionDerivation triangularPrismOddTseitinCNF c23 :=
    .initial c23 (by decide)
  have d24 : SetResolutionDerivation triangularPrismOddTseitinCNF c24 :=
    .initial c24 (by decide)
  have d25 : SetResolutionDerivation triangularPrismOddTseitinCNF c25 :=
    .resolve 7 c7 c24 c25
      (by decide) (by decide) (by decide) d7 d24
  have d26 : SetResolutionDerivation triangularPrismOddTseitinCNF c26 :=
    .resolve 6 c23 c25 c26
      (by decide) (by decide) (by decide) d23 d25
  have d27 : SetResolutionDerivation triangularPrismOddTseitinCNF c27 :=
    .initial c27 (by decide)
  have d28 : SetResolutionDerivation triangularPrismOddTseitinCNF c28 :=
    .initial c28 (by decide)
  have d29 : SetResolutionDerivation triangularPrismOddTseitinCNF c29 :=
    .resolve 7 c28 c2 c29
      (by decide) (by decide) (by decide) d28 d2
  have d30 : SetResolutionDerivation triangularPrismOddTseitinCNF c30 :=
    .resolve 6 c29 c27 c30
      (by decide) (by decide) (by decide) d29 d27
  have d31 : SetResolutionDerivation triangularPrismOddTseitinCNF c31 :=
    .resolve 8 c30 c26 c31
      (by decide) (by decide) (by decide) d30 d26
  have d32 : SetResolutionDerivation triangularPrismOddTseitinCNF c32 :=
    .initial c32 (by decide)
  have d33 : SetResolutionDerivation triangularPrismOddTseitinCNF c33 :=
    .initial c33 (by decide)
  have d34 : SetResolutionDerivation triangularPrismOddTseitinCNF c34 :=
    .resolve 1 c18 c33 c34
      (by decide) (by decide) (by decide) d18 d33
  have d35 : SetResolutionDerivation triangularPrismOddTseitinCNF c35 :=
    .resolve 0 c34 c32 c35
      (by decide) (by decide) (by decide) d34 d32
  have d36 : SetResolutionDerivation triangularPrismOddTseitinCNF c36 :=
    .initial c36 (by decide)
  have d37 : SetResolutionDerivation triangularPrismOddTseitinCNF c37 :=
    .initial c37 (by decide)
  have d38 : SetResolutionDerivation triangularPrismOddTseitinCNF c38 :=
    .resolve 0 c37 c11 c38
      (by decide) (by decide) (by decide) d37 d11
  have d39 : SetResolutionDerivation triangularPrismOddTseitinCNF c39 :=
    .resolve 1 c36 c38 c39
      (by decide) (by decide) (by decide) d36 d38
  have d40 : SetResolutionDerivation triangularPrismOddTseitinCNF c40 :=
    .resolve 3 c35 c39 c40
      (by decide) (by decide) (by decide) d35 d39
  have d41 : SetResolutionDerivation triangularPrismOddTseitinCNF c41 :=
    .resolve 5 c40 c31 c41
      (by decide) (by decide) (by decide) d40 d31
  have d42 : SetResolutionDerivation triangularPrismOddTseitinCNF c42 :=
    .resolve 4 c41 c22 c42
      (by decide) (by decide) (by decide) d41 d22
  have d43 : SetResolutionDerivation triangularPrismOddTseitinCNF c43 :=
    .initial c43 (by decide)
  have d44 : SetResolutionDerivation triangularPrismOddTseitinCNF c44 :=
    .resolve 6 c23 c43 c44
      (by decide) (by decide) (by decide) d23 d43
  have d45 : SetResolutionDerivation triangularPrismOddTseitinCNF c45 :=
    .resolve 7 c0 c44 c45
      (by decide) (by decide) (by decide) d0 d44
  have d46 : SetResolutionDerivation triangularPrismOddTseitinCNF c46 :=
    .initial c46 (by decide)
  have d47 : SetResolutionDerivation triangularPrismOddTseitinCNF c47 :=
    .resolve 6 c46 c27 c47
      (by decide) (by decide) (by decide) d46 d27
  have d48 : SetResolutionDerivation triangularPrismOddTseitinCNF c48 :=
    .resolve 7 c47 c5 c48
      (by decide) (by decide) (by decide) d47 d5
  have d49 : SetResolutionDerivation triangularPrismOddTseitinCNF c49 :=
    .resolve 8 c48 c45 c49
      (by decide) (by decide) (by decide) d48 d45
  have d50 : SetResolutionDerivation triangularPrismOddTseitinCNF c50 :=
    .initial c50 (by decide)
  have d51 : SetResolutionDerivation triangularPrismOddTseitinCNF c51 :=
    .resolve 1 c50 c33 c51
      (by decide) (by decide) (by decide) d50 d33
  have d52 : SetResolutionDerivation triangularPrismOddTseitinCNF c52 :=
    .resolve 0 c13 c51 c52
      (by decide) (by decide) (by decide) d13 d51
  have d53 : SetResolutionDerivation triangularPrismOddTseitinCNF c53 :=
    .initial c53 (by decide)
  have d54 : SetResolutionDerivation triangularPrismOddTseitinCNF c54 :=
    .resolve 0 c53 c17 c54
      (by decide) (by decide) (by decide) d53 d17
  have d55 : SetResolutionDerivation triangularPrismOddTseitinCNF c55 :=
    .resolve 1 c36 c54 c55
      (by decide) (by decide) (by decide) d36 d54
  have d56 : SetResolutionDerivation triangularPrismOddTseitinCNF c56 :=
    .resolve 3 c52 c55 c56
      (by decide) (by decide) (by decide) d52 d55
  have d57 : SetResolutionDerivation triangularPrismOddTseitinCNF c57 :=
    .resolve 4 c49 c56 c57
      (by decide) (by decide) (by decide) d49 d56
  have d58 : SetResolutionDerivation triangularPrismOddTseitinCNF c58 :=
    .resolve 8 c6 c24 c58
      (by decide) (by decide) (by decide) d6 d24
  have d59 : SetResolutionDerivation triangularPrismOddTseitinCNF c59 :=
    .resolve 7 c46 c58 c59
      (by decide) (by decide) (by decide) d46 d58
  have d60 : SetResolutionDerivation triangularPrismOddTseitinCNF c60 :=
    .resolve 8 c28 c1 c60
      (by decide) (by decide) (by decide) d28 d1
  have d61 : SetResolutionDerivation triangularPrismOddTseitinCNF c61 :=
    .resolve 7 c60 c43 c61
      (by decide) (by decide) (by decide) d60 d43
  have d62 : SetResolutionDerivation triangularPrismOddTseitinCNF c62 :=
    .resolve 6 c59 c61 c62
      (by decide) (by decide) (by decide) d59 d61
  have d63 : SetResolutionDerivation triangularPrismOddTseitinCNF c63 :=
    .resolve 3 c32 c12 c63
      (by decide) (by decide) (by decide) d32 d12
  have d64 : SetResolutionDerivation triangularPrismOddTseitinCNF c64 :=
    .resolve 0 c53 c63 c64
      (by decide) (by decide) (by decide) d53 d63
  have d65 : SetResolutionDerivation triangularPrismOddTseitinCNF c65 :=
    .resolve 0 c37 c50 c65
      (by decide) (by decide) (by decide) d37 d50
  have d66 : SetResolutionDerivation triangularPrismOddTseitinCNF c66 :=
    .resolve 3 c16 c65 c66
      (by decide) (by decide) (by decide) d16 d65
  have d67 : SetResolutionDerivation triangularPrismOddTseitinCNF c67 :=
    .resolve 1 c66 c64 c67
      (by decide) (by decide) (by decide) d66 d64
  have d68 : SetResolutionDerivation triangularPrismOddTseitinCNF c68 :=
    .resolve 4 c67 c62 c68
      (by decide) (by decide) (by decide) d67 d62
  have d69 : SetResolutionDerivation triangularPrismOddTseitinCNF c69 :=
    .resolve 5 c57 c68 c69
      (by decide) (by decide) (by decide) d57 d68
  have d70 : SetResolutionDerivation triangularPrismOddTseitinCNF c70 :=
    .resolve 2 c42 c69 c70
      (by decide) (by decide) (by decide) d42 d69
  exact d70

theorem triangular_prism_set_resolution_certificate_unsat :
    ¬ ∃ assignment,
      evalCNF assignment triangularPrismOddTseitinCNF = true :=
  set_resolution_refutation_unsat triangularPrismOddTseitinCNF
    triangular_prism_set_resolution_certificate

end AlexandriaComplexity
