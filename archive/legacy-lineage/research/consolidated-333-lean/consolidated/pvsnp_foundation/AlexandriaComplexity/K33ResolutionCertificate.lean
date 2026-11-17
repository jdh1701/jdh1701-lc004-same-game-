import AlexandriaComplexity.SetResolution

namespace AlexandriaComplexity

/-!
Generated from the frozen odd-charge cubic-family receipt.
This exact finite certificate is not an asymptotic lower bound and
has no P-versus-NP consequence.
-/

private abbrev p (index : Nat) : Literal := positiveLiteral index
private abbrev n (index : Nat) : Literal := negativeLiteral index

def k33FamilyJsonSHA256 : String :=
  "113ff703f70e762586fadf67a4bd0f22415905f706dbb08aa71d40bdbf8a9df2"

def k33FormulaSHA256 : String :=
  "675f243bb5f2228551d3206c42b8117038d5b8c063f5c6eccb201a90b460ca50"

def k33OddTseitinCNF : CNF := [
  [p 0, p 1, p 2],
  [p 0, n 1, n 2],
  [n 0, p 1, n 2],
  [n 0, n 1, p 2],
  [p 3, p 4, n 5],
  [p 3, n 4, p 5],
  [n 3, p 4, p 5],
  [n 3, n 4, n 5],
  [p 6, p 7, n 8],
  [p 6, n 7, p 8],
  [n 6, p 7, p 8],
  [n 6, n 7, n 8],
  [p 0, p 3, n 6],
  [p 0, n 3, p 6],
  [n 0, p 3, p 6],
  [n 0, n 3, n 6],
  [p 1, p 4, n 7],
  [p 1, n 4, p 7],
  [n 1, p 4, p 7],
  [n 1, n 4, n 7],
  [p 2, p 5, n 8],
  [p 2, n 5, p 8],
  [n 2, p 5, p 8],
  [n 2, n 5, n 8]
]

theorem k33_set_resolution_certificate :
    SetResolutionDerivation k33OddTseitinCNF [] := by
  let c0 : Clause := [p 0, n 1, n 2]
  let c1 : Clause := [p 1, n 4, p 7]
  let c2 : Clause := [p 0, n 2, n 4, p 7]
  let c3 : Clause := [n 3, n 4, n 5]
  let c4 : Clause := [n 0, p 3, p 6]
  let c5 : Clause := [n 0, n 4, n 5, p 6]
  let c6 : Clause := [n 2, p 5, p 8]
  let c7 : Clause := [p 6, p 7, n 8]
  let c8 : Clause := [n 2, p 5, p 6, p 7]
  let c9 : Clause := [n 0, n 2, n 4, p 6, p 7]
  let c10 : Clause := [n 2, n 4, p 6, p 7]
  let c11 : Clause := [p 3, p 4, n 5]
  let c12 : Clause := [n 2, p 3, p 4, p 8]
  let c13 : Clause := [n 2, p 3, p 4, p 6, p 7]
  let c14 : Clause := [p 0, n 3, p 6]
  let c15 : Clause := [n 1, p 4, p 7]
  let c16 : Clause := [n 0, p 1, n 2]
  let c17 : Clause := [n 0, n 2, p 4, p 7]
  let c18 : Clause := [n 2, n 3, p 4, p 6, p 7]
  let c19 : Clause := [n 2, p 4, p 6, p 7]
  let c20 : Clause := [n 2, p 6, p 7]
  let c21 : Clause := [n 0, n 3, n 6]
  let c22 : Clause := [n 1, n 2, n 3, n 6]
  let c23 : Clause := [n 6, p 7, p 8]
  let c24 : Clause := [n 2, n 5, n 8]
  let c25 : Clause := [n 2, n 5, n 6, p 7]
  let c26 : Clause := [n 3, p 4, p 5]
  let c27 : Clause := [p 1, n 3, p 5, p 7]
  let c28 : Clause := [p 1, n 2, n 3, n 6, p 7]
  let c29 : Clause := [n 2, n 3, n 6, p 7]
  let c30 : Clause := [p 3, n 4, p 5]
  let c31 : Clause := [n 2, p 3, n 4, n 6, p 7]
  let c32 : Clause := [p 0, p 3, n 6]
  let c33 : Clause := [n 2, p 3, p 4, n 6, p 7]
  let c34 : Clause := [n 2, p 3, n 6, p 7]
  let c35 : Clause := [n 2, n 6, p 7]
  let c36 : Clause := [n 2, p 7]
  let c37 : Clause := [p 2, p 5, n 8]
  let c38 : Clause := [p 0, n 3, p 7, p 8]
  let c39 : Clause := [p 0, p 2, n 3, p 5, p 7]
  let c40 : Clause := [p 0, p 1, p 2]
  let c41 : Clause := [p 0, p 2, p 4, p 7]
  let c42 : Clause := [p 0, p 2, p 3, p 5, p 7]
  let c43 : Clause := [p 0, p 2, p 5, p 7]
  let c44 : Clause := [p 2, n 5, p 8]
  let c45 : Clause := [p 2, n 5, p 6, p 7]
  let c46 : Clause := [p 0, n 4, n 5, n 6]
  let c47 : Clause := [p 0, p 2, n 5, n 6, p 7]
  let c48 : Clause := [p 0, p 2, n 5, p 7]
  let c49 : Clause := [p 0, p 2, p 7]
  let c50 : Clause := [n 0, n 1, p 2]
  let c51 : Clause := [n 0, p 2, n 3, p 5, p 7]
  let c52 : Clause := [n 0, n 3, p 7, n 8]
  let c53 : Clause := [n 0, p 2, n 3, n 5, p 7]
  let c54 : Clause := [n 0, p 2, n 3, p 7]
  let c55 : Clause := [n 0, p 3, p 7, p 8]
  let c56 : Clause := [n 0, p 2, p 3, p 5, p 7]
  let c57 : Clause := [n 0, p 2, n 4, p 7]
  let c58 : Clause := [n 0, p 2, p 3, n 5, p 7]
  let c59 : Clause := [n 0, p 2, p 3, p 7]
  let c60 : Clause := [n 0, p 2, p 7]
  let c61 : Clause := [p 2, p 7]
  let c62 : Clause := [p 7]
  let c63 : Clause := [p 1, p 4, n 7]
  let c64 : Clause := [p 0, n 2, p 4, n 7]
  let c65 : Clause := [n 0, p 4, p 5, p 6]
  let c66 : Clause := [p 6, n 7, p 8]
  let c67 : Clause := [n 2, n 5, p 6, n 7]
  let c68 : Clause := [n 0, n 2, p 4, p 6, n 7]
  let c69 : Clause := [n 2, p 4, p 6, n 7]
  let c70 : Clause := [n 2, p 3, n 4, n 8]
  let c71 : Clause := [n 2, p 3, n 4, p 6, n 7]
  let c72 : Clause := [n 1, n 4, n 7]
  let c73 : Clause := [n 0, n 2, n 4, n 7]
  let c74 : Clause := [n 2, n 3, n 4, p 6, n 7]
  let c75 : Clause := [n 2, n 4, p 6, n 7]
  let c76 : Clause := [n 2, p 6, n 7]
  let c77 : Clause := [n 6, n 7, n 8]
  let c78 : Clause := [n 2, p 5, n 6, n 7]
  let c79 : Clause := [p 1, n 3, n 5, n 7]
  let c80 : Clause := [p 1, n 2, n 3, n 6, n 7]
  let c81 : Clause := [n 2, n 3, n 6, n 7]
  let c82 : Clause := [n 2, p 3, p 4, n 6, n 7]
  let c83 : Clause := [n 2, p 3, n 4, n 6, n 7]
  let c84 : Clause := [n 2, p 3, n 6, n 7]
  let c85 : Clause := [n 2, n 6, n 7]
  let c86 : Clause := [n 2, n 7]
  let c87 : Clause := [p 0, n 3, n 7, n 8]
  let c88 : Clause := [p 0, p 2, n 3, n 5, n 7]
  let c89 : Clause := [p 0, p 2, n 4, n 7]
  let c90 : Clause := [p 0, p 2, p 3, n 5, n 7]
  let c91 : Clause := [p 0, p 2, n 5, n 7]
  let c92 : Clause := [p 2, p 5, p 6, n 7]
  let c93 : Clause := [p 0, p 4, p 5, n 6]
  let c94 : Clause := [p 0, p 2, p 5, n 6, n 7]
  let c95 : Clause := [p 0, p 2, p 5, n 7]
  let c96 : Clause := [p 0, p 2, n 7]
  let c97 : Clause := [n 0, p 2, n 3, n 5, n 7]
  let c98 : Clause := [n 0, n 3, n 7, p 8]
  let c99 : Clause := [n 0, p 2, n 3, p 5, n 7]
  let c100 : Clause := [n 0, p 2, n 3, n 7]
  let c101 : Clause := [n 0, p 3, n 7, n 8]
  let c102 : Clause := [n 0, p 2, p 3, n 5, n 7]
  let c103 : Clause := [n 0, p 2, p 4, n 7]
  let c104 : Clause := [n 0, p 2, p 3, p 5, n 7]
  let c105 : Clause := [n 0, p 2, p 3, n 7]
  let c106 : Clause := [n 0, p 2, n 7]
  let c107 : Clause := [p 2, n 7]
  let c108 : Clause := [n 7]
  let c109 : Clause := []

  have d0 : SetResolutionDerivation k33OddTseitinCNF c0 :=
    .initial c0 (by decide)
  have d1 : SetResolutionDerivation k33OddTseitinCNF c1 :=
    .initial c1 (by decide)
  have d2 : SetResolutionDerivation k33OddTseitinCNF c2 :=
    .resolve 1 c1 c0 c2
      (by decide) (by decide) (by decide) d1 d0
  have d3 : SetResolutionDerivation k33OddTseitinCNF c3 :=
    .initial c3 (by decide)
  have d4 : SetResolutionDerivation k33OddTseitinCNF c4 :=
    .initial c4 (by decide)
  have d5 : SetResolutionDerivation k33OddTseitinCNF c5 :=
    .resolve 3 c4 c3 c5
      (by decide) (by decide) (by decide) d4 d3
  have d6 : SetResolutionDerivation k33OddTseitinCNF c6 :=
    .initial c6 (by decide)
  have d7 : SetResolutionDerivation k33OddTseitinCNF c7 :=
    .initial c7 (by decide)
  have d8 : SetResolutionDerivation k33OddTseitinCNF c8 :=
    .resolve 8 c6 c7 c8
      (by decide) (by decide) (by decide) d6 d7
  have d9 : SetResolutionDerivation k33OddTseitinCNF c9 :=
    .resolve 5 c8 c5 c9
      (by decide) (by decide) (by decide) d8 d5
  have d10 : SetResolutionDerivation k33OddTseitinCNF c10 :=
    .resolve 0 c2 c9 c10
      (by decide) (by decide) (by decide) d2 d9
  have d11 : SetResolutionDerivation k33OddTseitinCNF c11 :=
    .initial c11 (by decide)
  have d12 : SetResolutionDerivation k33OddTseitinCNF c12 :=
    .resolve 5 c6 c11 c12
      (by decide) (by decide) (by decide) d6 d11
  have d13 : SetResolutionDerivation k33OddTseitinCNF c13 :=
    .resolve 8 c12 c7 c13
      (by decide) (by decide) (by decide) d12 d7
  have d14 : SetResolutionDerivation k33OddTseitinCNF c14 :=
    .initial c14 (by decide)
  have d15 : SetResolutionDerivation k33OddTseitinCNF c15 :=
    .initial c15 (by decide)
  have d16 : SetResolutionDerivation k33OddTseitinCNF c16 :=
    .initial c16 (by decide)
  have d17 : SetResolutionDerivation k33OddTseitinCNF c17 :=
    .resolve 1 c16 c15 c17
      (by decide) (by decide) (by decide) d16 d15
  have d18 : SetResolutionDerivation k33OddTseitinCNF c18 :=
    .resolve 0 c14 c17 c18
      (by decide) (by decide) (by decide) d14 d17
  have d19 : SetResolutionDerivation k33OddTseitinCNF c19 :=
    .resolve 3 c13 c18 c19
      (by decide) (by decide) (by decide) d13 d18
  have d20 : SetResolutionDerivation k33OddTseitinCNF c20 :=
    .resolve 4 c19 c10 c20
      (by decide) (by decide) (by decide) d19 d10
  have d21 : SetResolutionDerivation k33OddTseitinCNF c21 :=
    .initial c21 (by decide)
  have d22 : SetResolutionDerivation k33OddTseitinCNF c22 :=
    .resolve 0 c0 c21 c22
      (by decide) (by decide) (by decide) d0 d21
  have d23 : SetResolutionDerivation k33OddTseitinCNF c23 :=
    .initial c23 (by decide)
  have d24 : SetResolutionDerivation k33OddTseitinCNF c24 :=
    .initial c24 (by decide)
  have d25 : SetResolutionDerivation k33OddTseitinCNF c25 :=
    .resolve 8 c23 c24 c25
      (by decide) (by decide) (by decide) d23 d24
  have d26 : SetResolutionDerivation k33OddTseitinCNF c26 :=
    .initial c26 (by decide)
  have d27 : SetResolutionDerivation k33OddTseitinCNF c27 :=
    .resolve 4 c26 c1 c27
      (by decide) (by decide) (by decide) d26 d1
  have d28 : SetResolutionDerivation k33OddTseitinCNF c28 :=
    .resolve 5 c27 c25 c28
      (by decide) (by decide) (by decide) d27 d25
  have d29 : SetResolutionDerivation k33OddTseitinCNF c29 :=
    .resolve 1 c28 c22 c29
      (by decide) (by decide) (by decide) d28 d22
  have d30 : SetResolutionDerivation k33OddTseitinCNF c30 :=
    .initial c30 (by decide)
  have d31 : SetResolutionDerivation k33OddTseitinCNF c31 :=
    .resolve 5 c30 c25 c31
      (by decide) (by decide) (by decide) d30 d25
  have d32 : SetResolutionDerivation k33OddTseitinCNF c32 :=
    .initial c32 (by decide)
  have d33 : SetResolutionDerivation k33OddTseitinCNF c33 :=
    .resolve 0 c32 c17 c33
      (by decide) (by decide) (by decide) d32 d17
  have d34 : SetResolutionDerivation k33OddTseitinCNF c34 :=
    .resolve 4 c33 c31 c34
      (by decide) (by decide) (by decide) d33 d31
  have d35 : SetResolutionDerivation k33OddTseitinCNF c35 :=
    .resolve 3 c34 c29 c35
      (by decide) (by decide) (by decide) d34 d29
  have d36 : SetResolutionDerivation k33OddTseitinCNF c36 :=
    .resolve 6 c20 c35 c36
      (by decide) (by decide) (by decide) d20 d35
  have d37 : SetResolutionDerivation k33OddTseitinCNF c37 :=
    .initial c37 (by decide)
  have d38 : SetResolutionDerivation k33OddTseitinCNF c38 :=
    .resolve 6 c14 c23 c38
      (by decide) (by decide) (by decide) d14 d23
  have d39 : SetResolutionDerivation k33OddTseitinCNF c39 :=
    .resolve 8 c38 c37 c39
      (by decide) (by decide) (by decide) d38 d37
  have d40 : SetResolutionDerivation k33OddTseitinCNF c40 :=
    .initial c40 (by decide)
  have d41 : SetResolutionDerivation k33OddTseitinCNF c41 :=
    .resolve 1 c40 c15 c41
      (by decide) (by decide) (by decide) d40 d15
  have d42 : SetResolutionDerivation k33OddTseitinCNF c42 :=
    .resolve 4 c41 c30 c42
      (by decide) (by decide) (by decide) d41 d30
  have d43 : SetResolutionDerivation k33OddTseitinCNF c43 :=
    .resolve 3 c42 c39 c43
      (by decide) (by decide) (by decide) d42 d39
  have d44 : SetResolutionDerivation k33OddTseitinCNF c44 :=
    .initial c44 (by decide)
  have d45 : SetResolutionDerivation k33OddTseitinCNF c45 :=
    .resolve 8 c44 c7 c45
      (by decide) (by decide) (by decide) d44 d7
  have d46 : SetResolutionDerivation k33OddTseitinCNF c46 :=
    .resolve 3 c32 c3 c46
      (by decide) (by decide) (by decide) d32 d3
  have d47 : SetResolutionDerivation k33OddTseitinCNF c47 :=
    .resolve 4 c41 c46 c47
      (by decide) (by decide) (by decide) d41 d46
  have d48 : SetResolutionDerivation k33OddTseitinCNF c48 :=
    .resolve 6 c45 c47 c48
      (by decide) (by decide) (by decide) d45 d47
  have d49 : SetResolutionDerivation k33OddTseitinCNF c49 :=
    .resolve 5 c43 c48 c49
      (by decide) (by decide) (by decide) d43 d48
  have d50 : SetResolutionDerivation k33OddTseitinCNF c50 :=
    .initial c50 (by decide)
  have d51 : SetResolutionDerivation k33OddTseitinCNF c51 :=
    .resolve 1 c27 c50 c51
      (by decide) (by decide) (by decide) d27 d50
  have d52 : SetResolutionDerivation k33OddTseitinCNF c52 :=
    .resolve 6 c7 c21 c52
      (by decide) (by decide) (by decide) d7 d21
  have d53 : SetResolutionDerivation k33OddTseitinCNF c53 :=
    .resolve 8 c44 c52 c53
      (by decide) (by decide) (by decide) d44 d52
  have d54 : SetResolutionDerivation k33OddTseitinCNF c54 :=
    .resolve 5 c51 c53 c54
      (by decide) (by decide) (by decide) d51 d53
  have d55 : SetResolutionDerivation k33OddTseitinCNF c55 :=
    .resolve 6 c4 c23 c55
      (by decide) (by decide) (by decide) d4 d23
  have d56 : SetResolutionDerivation k33OddTseitinCNF c56 :=
    .resolve 8 c55 c37 c56
      (by decide) (by decide) (by decide) d55 d37
  have d57 : SetResolutionDerivation k33OddTseitinCNF c57 :=
    .resolve 1 c1 c50 c57
      (by decide) (by decide) (by decide) d1 d50
  have d58 : SetResolutionDerivation k33OddTseitinCNF c58 :=
    .resolve 4 c11 c57 c58
      (by decide) (by decide) (by decide) d11 d57
  have d59 : SetResolutionDerivation k33OddTseitinCNF c59 :=
    .resolve 5 c56 c58 c59
      (by decide) (by decide) (by decide) d56 d58
  have d60 : SetResolutionDerivation k33OddTseitinCNF c60 :=
    .resolve 3 c59 c54 c60
      (by decide) (by decide) (by decide) d59 d54
  have d61 : SetResolutionDerivation k33OddTseitinCNF c61 :=
    .resolve 0 c49 c60 c61
      (by decide) (by decide) (by decide) d49 d60
  have d62 : SetResolutionDerivation k33OddTseitinCNF c62 :=
    .resolve 2 c61 c36 c62
      (by decide) (by decide) (by decide) d61 d36
  have d63 : SetResolutionDerivation k33OddTseitinCNF c63 :=
    .initial c63 (by decide)
  have d64 : SetResolutionDerivation k33OddTseitinCNF c64 :=
    .resolve 1 c63 c0 c64
      (by decide) (by decide) (by decide) d63 d0
  have d65 : SetResolutionDerivation k33OddTseitinCNF c65 :=
    .resolve 3 c4 c26 c65
      (by decide) (by decide) (by decide) d4 d26
  have d66 : SetResolutionDerivation k33OddTseitinCNF c66 :=
    .initial c66 (by decide)
  have d67 : SetResolutionDerivation k33OddTseitinCNF c67 :=
    .resolve 8 c66 c24 c67
      (by decide) (by decide) (by decide) d66 d24
  have d68 : SetResolutionDerivation k33OddTseitinCNF c68 :=
    .resolve 5 c65 c67 c68
      (by decide) (by decide) (by decide) d65 d67
  have d69 : SetResolutionDerivation k33OddTseitinCNF c69 :=
    .resolve 0 c64 c68 c69
      (by decide) (by decide) (by decide) d64 d68
  have d70 : SetResolutionDerivation k33OddTseitinCNF c70 :=
    .resolve 5 c30 c24 c70
      (by decide) (by decide) (by decide) d30 d24
  have d71 : SetResolutionDerivation k33OddTseitinCNF c71 :=
    .resolve 8 c66 c70 c71
      (by decide) (by decide) (by decide) d66 d70
  have d72 : SetResolutionDerivation k33OddTseitinCNF c72 :=
    .initial c72 (by decide)
  have d73 : SetResolutionDerivation k33OddTseitinCNF c73 :=
    .resolve 1 c16 c72 c73
      (by decide) (by decide) (by decide) d16 d72
  have d74 : SetResolutionDerivation k33OddTseitinCNF c74 :=
    .resolve 0 c14 c73 c74
      (by decide) (by decide) (by decide) d14 d73
  have d75 : SetResolutionDerivation k33OddTseitinCNF c75 :=
    .resolve 3 c71 c74 c75
      (by decide) (by decide) (by decide) d71 d74
  have d76 : SetResolutionDerivation k33OddTseitinCNF c76 :=
    .resolve 4 c69 c75 c76
      (by decide) (by decide) (by decide) d69 d75
  have d77 : SetResolutionDerivation k33OddTseitinCNF c77 :=
    .initial c77 (by decide)
  have d78 : SetResolutionDerivation k33OddTseitinCNF c78 :=
    .resolve 8 c6 c77 c78
      (by decide) (by decide) (by decide) d6 d77
  have d79 : SetResolutionDerivation k33OddTseitinCNF c79 :=
    .resolve 4 c63 c3 c79
      (by decide) (by decide) (by decide) d63 d3
  have d80 : SetResolutionDerivation k33OddTseitinCNF c80 :=
    .resolve 5 c78 c79 c80
      (by decide) (by decide) (by decide) d78 d79
  have d81 : SetResolutionDerivation k33OddTseitinCNF c81 :=
    .resolve 1 c80 c22 c81
      (by decide) (by decide) (by decide) d80 d22
  have d82 : SetResolutionDerivation k33OddTseitinCNF c82 :=
    .resolve 5 c78 c11 c82
      (by decide) (by decide) (by decide) d78 d11
  have d83 : SetResolutionDerivation k33OddTseitinCNF c83 :=
    .resolve 0 c32 c73 c83
      (by decide) (by decide) (by decide) d32 d73
  have d84 : SetResolutionDerivation k33OddTseitinCNF c84 :=
    .resolve 4 c82 c83 c84
      (by decide) (by decide) (by decide) d82 d83
  have d85 : SetResolutionDerivation k33OddTseitinCNF c85 :=
    .resolve 3 c84 c81 c85
      (by decide) (by decide) (by decide) d84 d81
  have d86 : SetResolutionDerivation k33OddTseitinCNF c86 :=
    .resolve 6 c76 c85 c86
      (by decide) (by decide) (by decide) d76 d85
  have d87 : SetResolutionDerivation k33OddTseitinCNF c87 :=
    .resolve 6 c14 c77 c87
      (by decide) (by decide) (by decide) d14 d77
  have d88 : SetResolutionDerivation k33OddTseitinCNF c88 :=
    .resolve 8 c44 c87 c88
      (by decide) (by decide) (by decide) d44 d87
  have d89 : SetResolutionDerivation k33OddTseitinCNF c89 :=
    .resolve 1 c40 c72 c89
      (by decide) (by decide) (by decide) d40 d72
  have d90 : SetResolutionDerivation k33OddTseitinCNF c90 :=
    .resolve 4 c11 c89 c90
      (by decide) (by decide) (by decide) d11 d89
  have d91 : SetResolutionDerivation k33OddTseitinCNF c91 :=
    .resolve 3 c90 c88 c91
      (by decide) (by decide) (by decide) d90 d88
  have d92 : SetResolutionDerivation k33OddTseitinCNF c92 :=
    .resolve 8 c66 c37 c92
      (by decide) (by decide) (by decide) d66 d37
  have d93 : SetResolutionDerivation k33OddTseitinCNF c93 :=
    .resolve 3 c32 c26 c93
      (by decide) (by decide) (by decide) d32 d26
  have d94 : SetResolutionDerivation k33OddTseitinCNF c94 :=
    .resolve 4 c93 c89 c94
      (by decide) (by decide) (by decide) d93 d89
  have d95 : SetResolutionDerivation k33OddTseitinCNF c95 :=
    .resolve 6 c92 c94 c95
      (by decide) (by decide) (by decide) d92 d94
  have d96 : SetResolutionDerivation k33OddTseitinCNF c96 :=
    .resolve 5 c95 c91 c96
      (by decide) (by decide) (by decide) d95 d91
  have d97 : SetResolutionDerivation k33OddTseitinCNF c97 :=
    .resolve 1 c79 c50 c97
      (by decide) (by decide) (by decide) d79 d50
  have d98 : SetResolutionDerivation k33OddTseitinCNF c98 :=
    .resolve 6 c66 c21 c98
      (by decide) (by decide) (by decide) d66 d21
  have d99 : SetResolutionDerivation k33OddTseitinCNF c99 :=
    .resolve 8 c98 c37 c99
      (by decide) (by decide) (by decide) d98 d37
  have d100 : SetResolutionDerivation k33OddTseitinCNF c100 :=
    .resolve 5 c99 c97 c100
      (by decide) (by decide) (by decide) d99 d97
  have d101 : SetResolutionDerivation k33OddTseitinCNF c101 :=
    .resolve 6 c4 c77 c101
      (by decide) (by decide) (by decide) d4 d77
  have d102 : SetResolutionDerivation k33OddTseitinCNF c102 :=
    .resolve 8 c44 c101 c102
      (by decide) (by decide) (by decide) d44 d101
  have d103 : SetResolutionDerivation k33OddTseitinCNF c103 :=
    .resolve 1 c63 c50 c103
      (by decide) (by decide) (by decide) d63 d50
  have d104 : SetResolutionDerivation k33OddTseitinCNF c104 :=
    .resolve 4 c103 c30 c104
      (by decide) (by decide) (by decide) d103 d30
  have d105 : SetResolutionDerivation k33OddTseitinCNF c105 :=
    .resolve 5 c104 c102 c105
      (by decide) (by decide) (by decide) d104 d102
  have d106 : SetResolutionDerivation k33OddTseitinCNF c106 :=
    .resolve 3 c105 c100 c106
      (by decide) (by decide) (by decide) d105 d100
  have d107 : SetResolutionDerivation k33OddTseitinCNF c107 :=
    .resolve 0 c96 c106 c107
      (by decide) (by decide) (by decide) d96 d106
  have d108 : SetResolutionDerivation k33OddTseitinCNF c108 :=
    .resolve 2 c107 c86 c108
      (by decide) (by decide) (by decide) d107 d86
  have d109 : SetResolutionDerivation k33OddTseitinCNF c109 :=
    .resolve 7 c62 c108 c109
      (by decide) (by decide) (by decide) d62 d108
  exact d109

theorem k33_set_resolution_certificate_unsat :
    ¬ ∃ assignment,
      evalCNF assignment k33OddTseitinCNF = true :=
  set_resolution_refutation_unsat k33OddTseitinCNF
    k33_set_resolution_certificate

end AlexandriaComplexity
