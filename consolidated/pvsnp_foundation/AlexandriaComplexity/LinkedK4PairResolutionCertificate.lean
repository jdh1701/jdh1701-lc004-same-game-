import AlexandriaComplexity.SetResolution

namespace AlexandriaComplexity

/-!
Generated from the frozen odd-charge cubic-family receipt.
This exact finite certificate is not an asymptotic lower bound and
has no P-versus-NP consequence.
-/

private abbrev p (index : Nat) : Literal := positiveLiteral index
private abbrev n (index : Nat) : Literal := negativeLiteral index

def linkedK4PairFamilyJsonSHA256 : String :=
  "68eeed81e2e688fadb003bbff328c50ece3d3387b44d4819787ce3bf9459221f"

def linkedK4PairFormulaSHA256 : String :=
  "d0b1109eb8f7bc3bb79bc6507090000ce1730b81f7b15784efc2c7ec5b4c02c2"

def linkedK4PairOddTseitinCNF : CNF := [
  [p 0, p 1, p 2],
  [p 0, n 1, n 2],
  [n 0, p 1, n 2],
  [n 0, n 1, p 2],
  [p 0, p 3, n 4],
  [p 0, n 3, p 4],
  [n 0, p 3, p 4],
  [n 0, n 3, n 4],
  [p 1, p 3, n 10],
  [p 1, n 3, p 10],
  [n 1, p 3, p 10],
  [n 1, n 3, n 10],
  [p 2, p 4, n 11],
  [p 2, n 4, p 11],
  [n 2, p 4, p 11],
  [n 2, n 4, n 11],
  [p 5, p 6, n 7],
  [p 5, n 6, p 7],
  [n 5, p 6, p 7],
  [n 5, n 6, n 7],
  [p 5, p 8, n 9],
  [p 5, n 8, p 9],
  [n 5, p 8, p 9],
  [n 5, n 8, n 9],
  [p 6, p 8, n 10],
  [p 6, n 8, p 10],
  [n 6, p 8, p 10],
  [n 6, n 8, n 10],
  [p 7, p 9, n 11],
  [p 7, n 9, p 11],
  [n 7, p 9, p 11],
  [n 7, n 9, n 11]
]

theorem linked_k4_pair_set_resolution_certificate :
    SetResolutionDerivation linkedK4PairOddTseitinCNF [] := by
  let c0 : Clause := [n 0, n 1, p 2]
  let c1 : Clause := [p 1, n 3, p 10]
  let c2 : Clause := [n 0, p 2, n 3, p 10]
  let c3 : Clause := [n 0, p 3, p 4]
  let c4 : Clause := [p 2, n 4, p 11]
  let c5 : Clause := [n 0, p 2, p 3, p 11]
  let c6 : Clause := [n 0, p 2, p 10, p 11]
  let c7 : Clause := [n 1, p 3, p 10]
  let c8 : Clause := [p 0, p 1, p 2]
  let c9 : Clause := [p 0, p 2, p 3, p 10]
  let c10 : Clause := [p 0, n 3, p 4]
  let c11 : Clause := [p 0, p 2, n 3, p 11]
  let c12 : Clause := [p 0, p 2, p 10, p 11]
  let c13 : Clause := [p 2, p 10, p 11]
  let c14 : Clause := [n 2, p 4, p 11]
  let c15 : Clause := [p 0, p 3, n 4]
  let c16 : Clause := [p 0, n 2, p 3, p 11]
  let c17 : Clause := [n 0, p 1, n 2]
  let c18 : Clause := [n 0, n 2, p 3, p 10]
  let c19 : Clause := [n 2, p 3, p 10, p 11]
  let c20 : Clause := [n 0, n 3, n 4]
  let c21 : Clause := [n 0, n 2, n 3, p 11]
  let c22 : Clause := [p 0, n 1, n 2]
  let c23 : Clause := [p 0, n 2, n 3, p 10]
  let c24 : Clause := [n 2, n 3, p 10, p 11]
  let c25 : Clause := [n 2, p 10, p 11]
  let c26 : Clause := [p 10, p 11]
  let c27 : Clause := [n 0, n 3, n 4]
  let c28 : Clause := [p 1, p 3, n 10]
  let c29 : Clause := [n 0, p 1, n 4, n 10]
  let c30 : Clause := [n 0, p 1, n 2]
  let c31 : Clause := [p 2, p 4, n 11]
  let c32 : Clause := [n 0, p 1, p 4, n 11]
  let c33 : Clause := [n 0, p 1, n 10, n 11]
  let c34 : Clause := [n 2, n 4, n 11]
  let c35 : Clause := [p 0, p 1, p 2]
  let c36 : Clause := [p 0, p 1, n 4, n 11]
  let c37 : Clause := [p 0, n 3, p 4]
  let c38 : Clause := [p 0, p 1, p 4, n 10]
  let c39 : Clause := [p 0, p 1, n 10, n 11]
  let c40 : Clause := [p 1, n 10, n 11]
  let c41 : Clause := [n 0, n 1, p 2]
  let c42 : Clause := [n 0, n 1, n 4, n 11]
  let c43 : Clause := [n 1, n 3, n 10]
  let c44 : Clause := [p 0, p 3, n 4]
  let c45 : Clause := [p 0, n 1, n 4, n 10]
  let c46 : Clause := [n 1, n 4, n 10, n 11]
  let c47 : Clause := [n 0, p 3, p 4]
  let c48 : Clause := [n 0, n 1, p 4, n 10]
  let c49 : Clause := [p 0, n 1, n 2]
  let c50 : Clause := [p 0, n 1, p 4, n 11]
  let c51 : Clause := [n 1, p 4, n 10, n 11]
  let c52 : Clause := [n 1, n 10, n 11]
  let c53 : Clause := [n 10, n 11]
  let c54 : Clause := [n 7, p 9, p 11]
  let c55 : Clause := [n 5, n 8, n 9]
  let c56 : Clause := [n 5, n 7, n 8, p 11]
  let c57 : Clause := [n 6, n 8, n 10]
  let c58 : Clause := [p 5, p 6, n 7]
  let c59 : Clause := [p 5, n 7, n 8, n 10]
  let c60 : Clause := [n 7, n 8, n 10, p 11]
  let c61 : Clause := [n 5, p 6, p 7]
  let c62 : Clause := [n 5, p 7, n 8, n 10]
  let c63 : Clause := [p 5, n 8, p 9]
  let c64 : Clause := [p 7, n 9, p 11]
  let c65 : Clause := [p 5, p 7, n 8, p 11]
  let c66 : Clause := [p 7, n 8, n 10, p 11]
  let c67 : Clause := [n 8, n 10, p 11]
  let c68 : Clause := [n 5, n 6, n 7]
  let c69 : Clause := [p 6, p 8, n 10]
  let c70 : Clause := [n 5, n 7, p 8, n 10]
  let c71 : Clause := [n 5, p 8, p 9]
  let c72 : Clause := [n 5, p 7, p 8, p 11]
  let c73 : Clause := [n 5, p 8, n 10, p 11]
  let c74 : Clause := [p 5, p 8, n 9]
  let c75 : Clause := [p 5, n 7, p 8, p 11]
  let c76 : Clause := [p 5, n 6, p 7]
  let c77 : Clause := [p 5, p 7, p 8, n 10]
  let c78 : Clause := [p 5, p 8, n 10, p 11]
  let c79 : Clause := [p 8, n 10, p 11]
  let c80 : Clause := [n 10, p 11]
  let c81 : Clause := [n 5, n 6, n 7]
  let c82 : Clause := [p 7, p 9, n 11]
  let c83 : Clause := [n 5, n 6, p 9, n 11]
  let c84 : Clause := [n 5, p 8, p 9]
  let c85 : Clause := [p 6, n 8, p 10]
  let c86 : Clause := [n 5, p 6, p 9, p 10]
  let c87 : Clause := [n 5, p 9, p 10, n 11]
  let c88 : Clause := [n 6, p 8, p 10]
  let c89 : Clause := [p 5, n 8, p 9]
  let c90 : Clause := [p 5, n 6, p 9, p 10]
  let c91 : Clause := [p 5, p 6, n 7]
  let c92 : Clause := [p 5, p 6, p 9, n 11]
  let c93 : Clause := [p 5, p 9, p 10, n 11]
  let c94 : Clause := [p 9, p 10, n 11]
  let c95 : Clause := [n 7, n 9, n 11]
  let c96 : Clause := [p 5, n 6, p 7]
  let c97 : Clause := [p 5, n 6, n 9, n 11]
  let c98 : Clause := [n 5, n 8, n 9]
  let c99 : Clause := [n 5, n 6, n 9, p 10]
  let c100 : Clause := [n 6, n 9, p 10, n 11]
  let c101 : Clause := [n 5, p 6, p 7]
  let c102 : Clause := [n 5, p 6, n 9, n 11]
  let c103 : Clause := [p 5, p 8, n 9]
  let c104 : Clause := [p 5, p 6, n 9, p 10]
  let c105 : Clause := [p 6, n 9, p 10, n 11]
  let c106 : Clause := [n 9, p 10, n 11]
  let c107 : Clause := [p 10, n 11]
  let c108 : Clause := [p 11]
  let c109 : Clause := [n 11]
  let c110 : Clause := []

  have d0 : SetResolutionDerivation linkedK4PairOddTseitinCNF c0 :=
    .initial c0 (by decide)
  have d1 : SetResolutionDerivation linkedK4PairOddTseitinCNF c1 :=
    .initial c1 (by decide)
  have d2 : SetResolutionDerivation linkedK4PairOddTseitinCNF c2 :=
    .resolve 1 c1 c0 c2
      (by decide) (by decide) (by decide) d1 d0
  have d3 : SetResolutionDerivation linkedK4PairOddTseitinCNF c3 :=
    .initial c3 (by decide)
  have d4 : SetResolutionDerivation linkedK4PairOddTseitinCNF c4 :=
    .initial c4 (by decide)
  have d5 : SetResolutionDerivation linkedK4PairOddTseitinCNF c5 :=
    .resolve 4 c3 c4 c5
      (by decide) (by decide) (by decide) d3 d4
  have d6 : SetResolutionDerivation linkedK4PairOddTseitinCNF c6 :=
    .resolve 3 c5 c2 c6
      (by decide) (by decide) (by decide) d5 d2
  have d7 : SetResolutionDerivation linkedK4PairOddTseitinCNF c7 :=
    .initial c7 (by decide)
  have d8 : SetResolutionDerivation linkedK4PairOddTseitinCNF c8 :=
    .initial c8 (by decide)
  have d9 : SetResolutionDerivation linkedK4PairOddTseitinCNF c9 :=
    .resolve 1 c8 c7 c9
      (by decide) (by decide) (by decide) d8 d7
  have d10 : SetResolutionDerivation linkedK4PairOddTseitinCNF c10 :=
    .initial c10 (by decide)
  have d11 : SetResolutionDerivation linkedK4PairOddTseitinCNF c11 :=
    .resolve 4 c10 c4 c11
      (by decide) (by decide) (by decide) d10 d4
  have d12 : SetResolutionDerivation linkedK4PairOddTseitinCNF c12 :=
    .resolve 3 c9 c11 c12
      (by decide) (by decide) (by decide) d9 d11
  have d13 : SetResolutionDerivation linkedK4PairOddTseitinCNF c13 :=
    .resolve 0 c12 c6 c13
      (by decide) (by decide) (by decide) d12 d6
  have d14 : SetResolutionDerivation linkedK4PairOddTseitinCNF c14 :=
    .initial c14 (by decide)
  have d15 : SetResolutionDerivation linkedK4PairOddTseitinCNF c15 :=
    .initial c15 (by decide)
  have d16 : SetResolutionDerivation linkedK4PairOddTseitinCNF c16 :=
    .resolve 4 c14 c15 c16
      (by decide) (by decide) (by decide) d14 d15
  have d17 : SetResolutionDerivation linkedK4PairOddTseitinCNF c17 :=
    .initial c17 (by decide)
  have d18 : SetResolutionDerivation linkedK4PairOddTseitinCNF c18 :=
    .resolve 1 c17 c7 c18
      (by decide) (by decide) (by decide) d17 d7
  have d19 : SetResolutionDerivation linkedK4PairOddTseitinCNF c19 :=
    .resolve 0 c16 c18 c19
      (by decide) (by decide) (by decide) d16 d18
  have d20 : SetResolutionDerivation linkedK4PairOddTseitinCNF c20 :=
    .initial c20 (by decide)
  have d21 : SetResolutionDerivation linkedK4PairOddTseitinCNF c21 :=
    .resolve 4 c14 c20 c21
      (by decide) (by decide) (by decide) d14 d20
  have d22 : SetResolutionDerivation linkedK4PairOddTseitinCNF c22 :=
    .initial c22 (by decide)
  have d23 : SetResolutionDerivation linkedK4PairOddTseitinCNF c23 :=
    .resolve 1 c1 c22 c23
      (by decide) (by decide) (by decide) d1 d22
  have d24 : SetResolutionDerivation linkedK4PairOddTseitinCNF c24 :=
    .resolve 0 c23 c21 c24
      (by decide) (by decide) (by decide) d23 d21
  have d25 : SetResolutionDerivation linkedK4PairOddTseitinCNF c25 :=
    .resolve 3 c19 c24 c25
      (by decide) (by decide) (by decide) d19 d24
  have d26 : SetResolutionDerivation linkedK4PairOddTseitinCNF c26 :=
    .resolve 2 c13 c25 c26
      (by decide) (by decide) (by decide) d13 d25
  have d27 : SetResolutionDerivation linkedK4PairOddTseitinCNF c27 :=
    .initial c27 (by decide)
  have d28 : SetResolutionDerivation linkedK4PairOddTseitinCNF c28 :=
    .initial c28 (by decide)
  have d29 : SetResolutionDerivation linkedK4PairOddTseitinCNF c29 :=
    .resolve 3 c28 c27 c29
      (by decide) (by decide) (by decide) d28 d27
  have d30 : SetResolutionDerivation linkedK4PairOddTseitinCNF c30 :=
    .initial c30 (by decide)
  have d31 : SetResolutionDerivation linkedK4PairOddTseitinCNF c31 :=
    .initial c31 (by decide)
  have d32 : SetResolutionDerivation linkedK4PairOddTseitinCNF c32 :=
    .resolve 2 c31 c30 c32
      (by decide) (by decide) (by decide) d31 d30
  have d33 : SetResolutionDerivation linkedK4PairOddTseitinCNF c33 :=
    .resolve 4 c32 c29 c33
      (by decide) (by decide) (by decide) d32 d29
  have d34 : SetResolutionDerivation linkedK4PairOddTseitinCNF c34 :=
    .initial c34 (by decide)
  have d35 : SetResolutionDerivation linkedK4PairOddTseitinCNF c35 :=
    .initial c35 (by decide)
  have d36 : SetResolutionDerivation linkedK4PairOddTseitinCNF c36 :=
    .resolve 2 c35 c34 c36
      (by decide) (by decide) (by decide) d35 d34
  have d37 : SetResolutionDerivation linkedK4PairOddTseitinCNF c37 :=
    .initial c37 (by decide)
  have d38 : SetResolutionDerivation linkedK4PairOddTseitinCNF c38 :=
    .resolve 3 c28 c37 c38
      (by decide) (by decide) (by decide) d28 d37
  have d39 : SetResolutionDerivation linkedK4PairOddTseitinCNF c39 :=
    .resolve 4 c38 c36 c39
      (by decide) (by decide) (by decide) d38 d36
  have d40 : SetResolutionDerivation linkedK4PairOddTseitinCNF c40 :=
    .resolve 0 c39 c33 c40
      (by decide) (by decide) (by decide) d39 d33
  have d41 : SetResolutionDerivation linkedK4PairOddTseitinCNF c41 :=
    .initial c41 (by decide)
  have d42 : SetResolutionDerivation linkedK4PairOddTseitinCNF c42 :=
    .resolve 2 c41 c34 c42
      (by decide) (by decide) (by decide) d41 d34
  have d43 : SetResolutionDerivation linkedK4PairOddTseitinCNF c43 :=
    .initial c43 (by decide)
  have d44 : SetResolutionDerivation linkedK4PairOddTseitinCNF c44 :=
    .initial c44 (by decide)
  have d45 : SetResolutionDerivation linkedK4PairOddTseitinCNF c45 :=
    .resolve 3 c44 c43 c45
      (by decide) (by decide) (by decide) d44 d43
  have d46 : SetResolutionDerivation linkedK4PairOddTseitinCNF c46 :=
    .resolve 0 c45 c42 c46
      (by decide) (by decide) (by decide) d45 d42
  have d47 : SetResolutionDerivation linkedK4PairOddTseitinCNF c47 :=
    .initial c47 (by decide)
  have d48 : SetResolutionDerivation linkedK4PairOddTseitinCNF c48 :=
    .resolve 3 c47 c43 c48
      (by decide) (by decide) (by decide) d47 d43
  have d49 : SetResolutionDerivation linkedK4PairOddTseitinCNF c49 :=
    .initial c49 (by decide)
  have d50 : SetResolutionDerivation linkedK4PairOddTseitinCNF c50 :=
    .resolve 2 c31 c49 c50
      (by decide) (by decide) (by decide) d31 d49
  have d51 : SetResolutionDerivation linkedK4PairOddTseitinCNF c51 :=
    .resolve 0 c50 c48 c51
      (by decide) (by decide) (by decide) d50 d48
  have d52 : SetResolutionDerivation linkedK4PairOddTseitinCNF c52 :=
    .resolve 4 c51 c46 c52
      (by decide) (by decide) (by decide) d51 d46
  have d53 : SetResolutionDerivation linkedK4PairOddTseitinCNF c53 :=
    .resolve 1 c40 c52 c53
      (by decide) (by decide) (by decide) d40 d52
  have d54 : SetResolutionDerivation linkedK4PairOddTseitinCNF c54 :=
    .initial c54 (by decide)
  have d55 : SetResolutionDerivation linkedK4PairOddTseitinCNF c55 :=
    .initial c55 (by decide)
  have d56 : SetResolutionDerivation linkedK4PairOddTseitinCNF c56 :=
    .resolve 9 c54 c55 c56
      (by decide) (by decide) (by decide) d54 d55
  have d57 : SetResolutionDerivation linkedK4PairOddTseitinCNF c57 :=
    .initial c57 (by decide)
  have d58 : SetResolutionDerivation linkedK4PairOddTseitinCNF c58 :=
    .initial c58 (by decide)
  have d59 : SetResolutionDerivation linkedK4PairOddTseitinCNF c59 :=
    .resolve 6 c58 c57 c59
      (by decide) (by decide) (by decide) d58 d57
  have d60 : SetResolutionDerivation linkedK4PairOddTseitinCNF c60 :=
    .resolve 5 c59 c56 c60
      (by decide) (by decide) (by decide) d59 d56
  have d61 : SetResolutionDerivation linkedK4PairOddTseitinCNF c61 :=
    .initial c61 (by decide)
  have d62 : SetResolutionDerivation linkedK4PairOddTseitinCNF c62 :=
    .resolve 6 c61 c57 c62
      (by decide) (by decide) (by decide) d61 d57
  have d63 : SetResolutionDerivation linkedK4PairOddTseitinCNF c63 :=
    .initial c63 (by decide)
  have d64 : SetResolutionDerivation linkedK4PairOddTseitinCNF c64 :=
    .initial c64 (by decide)
  have d65 : SetResolutionDerivation linkedK4PairOddTseitinCNF c65 :=
    .resolve 9 c63 c64 c65
      (by decide) (by decide) (by decide) d63 d64
  have d66 : SetResolutionDerivation linkedK4PairOddTseitinCNF c66 :=
    .resolve 5 c65 c62 c66
      (by decide) (by decide) (by decide) d65 d62
  have d67 : SetResolutionDerivation linkedK4PairOddTseitinCNF c67 :=
    .resolve 7 c66 c60 c67
      (by decide) (by decide) (by decide) d66 d60
  have d68 : SetResolutionDerivation linkedK4PairOddTseitinCNF c68 :=
    .initial c68 (by decide)
  have d69 : SetResolutionDerivation linkedK4PairOddTseitinCNF c69 :=
    .initial c69 (by decide)
  have d70 : SetResolutionDerivation linkedK4PairOddTseitinCNF c70 :=
    .resolve 6 c69 c68 c70
      (by decide) (by decide) (by decide) d69 d68
  have d71 : SetResolutionDerivation linkedK4PairOddTseitinCNF c71 :=
    .initial c71 (by decide)
  have d72 : SetResolutionDerivation linkedK4PairOddTseitinCNF c72 :=
    .resolve 9 c71 c64 c72
      (by decide) (by decide) (by decide) d71 d64
  have d73 : SetResolutionDerivation linkedK4PairOddTseitinCNF c73 :=
    .resolve 7 c72 c70 c73
      (by decide) (by decide) (by decide) d72 d70
  have d74 : SetResolutionDerivation linkedK4PairOddTseitinCNF c74 :=
    .initial c74 (by decide)
  have d75 : SetResolutionDerivation linkedK4PairOddTseitinCNF c75 :=
    .resolve 9 c54 c74 c75
      (by decide) (by decide) (by decide) d54 d74
  have d76 : SetResolutionDerivation linkedK4PairOddTseitinCNF c76 :=
    .initial c76 (by decide)
  have d77 : SetResolutionDerivation linkedK4PairOddTseitinCNF c77 :=
    .resolve 6 c69 c76 c77
      (by decide) (by decide) (by decide) d69 d76
  have d78 : SetResolutionDerivation linkedK4PairOddTseitinCNF c78 :=
    .resolve 7 c77 c75 c78
      (by decide) (by decide) (by decide) d77 d75
  have d79 : SetResolutionDerivation linkedK4PairOddTseitinCNF c79 :=
    .resolve 5 c78 c73 c79
      (by decide) (by decide) (by decide) d78 d73
  have d80 : SetResolutionDerivation linkedK4PairOddTseitinCNF c80 :=
    .resolve 8 c79 c67 c80
      (by decide) (by decide) (by decide) d79 d67
  have d81 : SetResolutionDerivation linkedK4PairOddTseitinCNF c81 :=
    .initial c81 (by decide)
  have d82 : SetResolutionDerivation linkedK4PairOddTseitinCNF c82 :=
    .initial c82 (by decide)
  have d83 : SetResolutionDerivation linkedK4PairOddTseitinCNF c83 :=
    .resolve 7 c82 c81 c83
      (by decide) (by decide) (by decide) d82 d81
  have d84 : SetResolutionDerivation linkedK4PairOddTseitinCNF c84 :=
    .initial c84 (by decide)
  have d85 : SetResolutionDerivation linkedK4PairOddTseitinCNF c85 :=
    .initial c85 (by decide)
  have d86 : SetResolutionDerivation linkedK4PairOddTseitinCNF c86 :=
    .resolve 8 c84 c85 c86
      (by decide) (by decide) (by decide) d84 d85
  have d87 : SetResolutionDerivation linkedK4PairOddTseitinCNF c87 :=
    .resolve 6 c86 c83 c87
      (by decide) (by decide) (by decide) d86 d83
  have d88 : SetResolutionDerivation linkedK4PairOddTseitinCNF c88 :=
    .initial c88 (by decide)
  have d89 : SetResolutionDerivation linkedK4PairOddTseitinCNF c89 :=
    .initial c89 (by decide)
  have d90 : SetResolutionDerivation linkedK4PairOddTseitinCNF c90 :=
    .resolve 8 c88 c89 c90
      (by decide) (by decide) (by decide) d88 d89
  have d91 : SetResolutionDerivation linkedK4PairOddTseitinCNF c91 :=
    .initial c91 (by decide)
  have d92 : SetResolutionDerivation linkedK4PairOddTseitinCNF c92 :=
    .resolve 7 c82 c91 c92
      (by decide) (by decide) (by decide) d82 d91
  have d93 : SetResolutionDerivation linkedK4PairOddTseitinCNF c93 :=
    .resolve 6 c92 c90 c93
      (by decide) (by decide) (by decide) d92 d90
  have d94 : SetResolutionDerivation linkedK4PairOddTseitinCNF c94 :=
    .resolve 5 c93 c87 c94
      (by decide) (by decide) (by decide) d93 d87
  have d95 : SetResolutionDerivation linkedK4PairOddTseitinCNF c95 :=
    .initial c95 (by decide)
  have d96 : SetResolutionDerivation linkedK4PairOddTseitinCNF c96 :=
    .initial c96 (by decide)
  have d97 : SetResolutionDerivation linkedK4PairOddTseitinCNF c97 :=
    .resolve 7 c96 c95 c97
      (by decide) (by decide) (by decide) d96 d95
  have d98 : SetResolutionDerivation linkedK4PairOddTseitinCNF c98 :=
    .initial c98 (by decide)
  have d99 : SetResolutionDerivation linkedK4PairOddTseitinCNF c99 :=
    .resolve 8 c88 c98 c99
      (by decide) (by decide) (by decide) d88 d98
  have d100 : SetResolutionDerivation linkedK4PairOddTseitinCNF c100 :=
    .resolve 5 c97 c99 c100
      (by decide) (by decide) (by decide) d97 d99
  have d101 : SetResolutionDerivation linkedK4PairOddTseitinCNF c101 :=
    .initial c101 (by decide)
  have d102 : SetResolutionDerivation linkedK4PairOddTseitinCNF c102 :=
    .resolve 7 c101 c95 c102
      (by decide) (by decide) (by decide) d101 d95
  have d103 : SetResolutionDerivation linkedK4PairOddTseitinCNF c103 :=
    .initial c103 (by decide)
  have d104 : SetResolutionDerivation linkedK4PairOddTseitinCNF c104 :=
    .resolve 8 c103 c85 c104
      (by decide) (by decide) (by decide) d103 d85
  have d105 : SetResolutionDerivation linkedK4PairOddTseitinCNF c105 :=
    .resolve 5 c104 c102 c105
      (by decide) (by decide) (by decide) d104 d102
  have d106 : SetResolutionDerivation linkedK4PairOddTseitinCNF c106 :=
    .resolve 6 c105 c100 c106
      (by decide) (by decide) (by decide) d105 d100
  have d107 : SetResolutionDerivation linkedK4PairOddTseitinCNF c107 :=
    .resolve 9 c94 c106 c107
      (by decide) (by decide) (by decide) d94 d106
  have d108 : SetResolutionDerivation linkedK4PairOddTseitinCNF c108 :=
    .resolve 10 c26 c80 c108
      (by decide) (by decide) (by decide) d26 d80
  have d109 : SetResolutionDerivation linkedK4PairOddTseitinCNF c109 :=
    .resolve 10 c107 c53 c109
      (by decide) (by decide) (by decide) d107 d53
  have d110 : SetResolutionDerivation linkedK4PairOddTseitinCNF c110 :=
    .resolve 11 c108 c109 c110
      (by decide) (by decide) (by decide) d108 d109
  exact d110

theorem linked_k4_pair_set_resolution_certificate_unsat :
    ¬ ∃ assignment,
      evalCNF assignment linkedK4PairOddTseitinCNF = true :=
  set_resolution_refutation_unsat linkedK4PairOddTseitinCNF
    linked_k4_pair_set_resolution_certificate

end AlexandriaComplexity
