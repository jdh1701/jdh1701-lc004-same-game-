import AlexandriaComplexity.WidthBoundedSetResolution

namespace AlexandriaComplexity

/-!
Unpromoted candidate from deterministic bounded elimination.
Independent Python replay passed; pinned Lean replay is pending.
This exact finite certificate is not an asymptotic lower bound and
has no P-versus-NP consequence.
-/

private abbrev p (index : Nat) : Literal := positiveLiteral index
private abbrev n (index : Nat) : Literal := negativeLiteral index

def wagnerM8FamilyJsonSHA256 : String :=
  "5590b16b47c09fc9520e8312f5155037ccd620d666783128a15b6f5180e24d38"

def wagnerM8FormulaSHA256 : String :=
  "1dcf455aae3950bee467d725f3145d600b0e26c44dfe80c0c5cbfde0a22d1ae2"

def wagnerM8OddTseitinCNF : CNF := [
  [p 0, p 7, p 8],
  [p 0, n 7, n 8],
  [n 0, p 7, n 8],
  [n 0, n 7, p 8],
  [p 0, p 1, n 9],
  [p 0, n 1, p 9],
  [n 0, p 1, p 9],
  [n 0, n 1, n 9],
  [p 1, p 2, n 10],
  [p 1, n 2, p 10],
  [n 1, p 2, p 10],
  [n 1, n 2, n 10],
  [p 2, p 3, n 11],
  [p 2, n 3, p 11],
  [n 2, p 3, p 11],
  [n 2, n 3, n 11],
  [p 3, p 4, n 8],
  [p 3, n 4, p 8],
  [n 3, p 4, p 8],
  [n 3, n 4, n 8],
  [p 4, p 5, n 9],
  [p 4, n 5, p 9],
  [n 4, p 5, p 9],
  [n 4, n 5, n 9],
  [p 5, p 6, n 10],
  [p 5, n 6, p 10],
  [n 5, p 6, p 10],
  [n 5, n 6, n 10],
  [p 6, p 7, n 11],
  [p 6, n 7, p 11],
  [n 6, p 7, p 11],
  [n 6, n 7, n 11]
]

theorem wagner_m8_width_five_certificate :
    WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 [] := by
  let c0 : Clause := [p 0, p 7, p 8]
  let c1 : Clause := [p 3, p 4, n 8]
  let c2 : Clause := [p 2, n 3, p 11]
  let c3 : Clause := [p 2, p 4, n 8, p 11]
  let c4 : Clause := [p 0, p 2, p 4, p 7, p 11]
  let c5 : Clause := [p 6, n 7, p 11]
  let c6 : Clause := [p 0, p 2, p 4, p 6, p 11]
  let c7 : Clause := [p 6, p 7, n 11]
  let c8 : Clause := [p 2, p 3, n 11]
  let c9 : Clause := [n 3, p 4, p 8]
  let c10 : Clause := [p 2, p 4, p 8, n 11]
  let c11 : Clause := [p 0, n 7, n 8]
  let c12 : Clause := [p 0, p 2, p 4, n 7, n 11]
  let c13 : Clause := [p 0, p 2, p 4, p 6, n 11]
  let c14 : Clause := [p 0, p 2, p 4, p 6]
  let c15 : Clause := [n 0, p 1, p 9]
  let c16 : Clause := [n 1, p 2, p 10]
  let c17 : Clause := [n 0, p 2, p 9, p 10]
  let c18 : Clause := [p 5, p 6, n 10]
  let c19 : Clause := [p 4, n 5, p 9]
  let c20 : Clause := [p 4, p 6, p 9, n 10]
  let c21 : Clause := [n 0, p 2, p 4, p 6, p 9]
  let c22 : Clause := [p 4, p 5, n 9]
  let c23 : Clause := [n 5, p 6, p 10]
  let c24 : Clause := [p 4, p 6, n 9, p 10]
  let c25 : Clause := [p 1, p 2, n 10]
  let c26 : Clause := [n 0, n 1, n 9]
  let c27 : Clause := [n 0, p 2, n 9, n 10]
  let c28 : Clause := [n 0, p 2, p 4, p 6, n 9]
  let c29 : Clause := [n 0, p 2, p 4, p 6]
  let c30 : Clause := [p 2, p 4, p 6]
  let c31 : Clause := [n 4, p 5, p 9]
  let c32 : Clause := [n 4, p 6, p 9, p 10]
  let c33 : Clause := [p 0, n 1, p 9]
  let c34 : Clause := [p 0, p 2, p 9, n 10]
  let c35 : Clause := [p 0, p 2, n 4, p 6, p 9]
  let c36 : Clause := [p 0, p 1, n 9]
  let c37 : Clause := [p 0, p 2, n 9, p 10]
  let c38 : Clause := [n 4, n 5, n 9]
  let c39 : Clause := [n 4, p 6, n 9, n 10]
  let c40 : Clause := [p 0, p 2, n 4, p 6, n 9]
  let c41 : Clause := [p 0, p 2, n 4, p 6]
  let c42 : Clause := [p 3, n 4, p 8]
  let c43 : Clause := [p 2, n 4, p 8, p 11]
  let c44 : Clause := [n 0, p 7, n 8]
  let c45 : Clause := [n 0, p 2, n 4, p 7, p 11]
  let c46 : Clause := [n 0, p 2, n 4, p 6, p 11]
  let c47 : Clause := [n 0, n 7, p 8]
  let c48 : Clause := [n 3, n 4, n 8]
  let c49 : Clause := [p 2, n 4, n 8, n 11]
  let c50 : Clause := [n 0, p 2, n 4, n 7, n 11]
  let c51 : Clause := [n 0, p 2, n 4, p 6, n 11]
  let c52 : Clause := [n 0, p 2, n 4, p 6]
  let c53 : Clause := [p 2, n 4, p 6]
  let c54 : Clause := [p 2, p 6]
  let c55 : Clause := [p 5, n 6, p 10]
  let c56 : Clause := [p 4, n 6, p 9, p 10]
  let c57 : Clause := [p 0, p 2, p 4, n 6, p 9]
  let c58 : Clause := [n 5, n 6, n 10]
  let c59 : Clause := [p 4, n 6, n 9, n 10]
  let c60 : Clause := [p 0, p 2, p 4, n 6, n 9]
  let c61 : Clause := [p 0, p 2, p 4, n 6]
  let c62 : Clause := [n 6, p 7, p 11]
  let c63 : Clause := [n 0, p 2, p 4, n 7, p 11]
  let c64 : Clause := [n 0, p 2, p 4, n 6, p 11]
  let c65 : Clause := [n 0, p 2, p 4, p 7, n 11]
  let c66 : Clause := [n 6, n 7, n 11]
  let c67 : Clause := [n 0, p 2, p 4, n 6, n 11]
  let c68 : Clause := [n 0, p 2, p 4, n 6]
  let c69 : Clause := [p 2, p 4, n 6]
  let c70 : Clause := [p 0, p 2, n 4, n 7, p 11]
  let c71 : Clause := [p 0, p 2, n 4, n 6, p 11]
  let c72 : Clause := [p 0, p 2, n 4, p 7, n 11]
  let c73 : Clause := [p 0, p 2, n 4, n 6, n 11]
  let c74 : Clause := [p 0, p 2, n 4, n 6]
  let c75 : Clause := [n 4, n 6, p 9, n 10]
  let c76 : Clause := [n 0, p 2, n 4, n 6, p 9]
  let c77 : Clause := [n 4, n 6, n 9, p 10]
  let c78 : Clause := [n 0, p 2, n 4, n 6, n 9]
  let c79 : Clause := [n 0, p 2, n 4, n 6]
  let c80 : Clause := [p 2, n 4, n 6]
  let c81 : Clause := [p 2, n 6]
  let c82 : Clause := [p 2]
  let c83 : Clause := [p 1, n 2, p 10]
  let c84 : Clause := [p 0, n 2, p 9, p 10]
  let c85 : Clause := [p 0, n 2, p 4, p 6, p 9]
  let c86 : Clause := [n 1, n 2, n 10]
  let c87 : Clause := [p 0, n 2, n 9, n 10]
  let c88 : Clause := [p 0, n 2, p 4, p 6, n 9]
  let c89 : Clause := [p 0, n 2, p 4, p 6]
  let c90 : Clause := [n 2, p 3, p 11]
  let c91 : Clause := [n 2, p 4, p 8, p 11]
  let c92 : Clause := [n 0, n 2, p 4, p 7, p 11]
  let c93 : Clause := [n 0, n 2, p 4, p 6, p 11]
  let c94 : Clause := [n 2, n 3, n 11]
  let c95 : Clause := [n 2, p 4, n 8, n 11]
  let c96 : Clause := [n 0, n 2, p 4, n 7, n 11]
  let c97 : Clause := [n 0, n 2, p 4, p 6, n 11]
  let c98 : Clause := [n 0, n 2, p 4, p 6]
  let c99 : Clause := [n 2, p 4, p 6]
  let c100 : Clause := [n 2, n 4, n 8, p 11]
  let c101 : Clause := [p 0, n 2, n 4, p 7, p 11]
  let c102 : Clause := [p 0, n 2, n 4, p 6, p 11]
  let c103 : Clause := [n 2, n 4, p 8, n 11]
  let c104 : Clause := [p 0, n 2, n 4, n 7, n 11]
  let c105 : Clause := [p 0, n 2, n 4, p 6, n 11]
  let c106 : Clause := [p 0, n 2, n 4, p 6]
  let c107 : Clause := [n 0, n 2, p 9, n 10]
  let c108 : Clause := [n 0, n 2, n 4, p 6, p 9]
  let c109 : Clause := [n 0, n 2, n 9, p 10]
  let c110 : Clause := [n 0, n 2, n 4, p 6, n 9]
  let c111 : Clause := [n 0, n 2, n 4, p 6]
  let c112 : Clause := [n 2, n 4, p 6]
  let c113 : Clause := [n 2, p 6]
  let c114 : Clause := [p 0, n 2, p 4, n 7, p 11]
  let c115 : Clause := [p 0, n 2, p 4, n 6, p 11]
  let c116 : Clause := [p 0, n 2, p 4, p 7, n 11]
  let c117 : Clause := [p 0, n 2, p 4, n 6, n 11]
  let c118 : Clause := [p 0, n 2, p 4, n 6]
  let c119 : Clause := [n 0, n 2, p 4, n 6, p 9]
  let c120 : Clause := [n 0, n 2, p 4, n 6, n 9]
  let c121 : Clause := [n 0, n 2, p 4, n 6]
  let c122 : Clause := [n 2, p 4, n 6]
  let c123 : Clause := [p 0, n 2, n 4, n 6, p 9]
  let c124 : Clause := [p 0, n 2, n 4, n 6, n 9]
  let c125 : Clause := [p 0, n 2, n 4, n 6]
  let c126 : Clause := [n 0, n 2, n 4, n 7, p 11]
  let c127 : Clause := [n 0, n 2, n 4, n 6, p 11]
  let c128 : Clause := [n 0, n 2, n 4, p 7, n 11]
  let c129 : Clause := [n 0, n 2, n 4, n 6, n 11]
  let c130 : Clause := [n 0, n 2, n 4, n 6]
  let c131 : Clause := [n 2, n 4, n 6]
  let c132 : Clause := [n 2, n 6]
  let c133 : Clause := [n 2]
  let c134 : Clause := []

  have d0 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c0 :=
    .initial c0 (by decide) (by decide)
  have d1 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c1 :=
    .initial c1 (by decide) (by decide)
  have d2 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c2 :=
    .initial c2 (by decide) (by decide)
  have d3 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c3 :=
    .resolve 3 c1 c2 c3
      (by decide) (by decide) (by decide) (by decide) d1 d2
  have d4 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c4 :=
    .resolve 8 c0 c3 c4
      (by decide) (by decide) (by decide) (by decide) d0 d3
  have d5 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c5 :=
    .initial c5 (by decide) (by decide)
  have d6 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c6 :=
    .resolve 7 c4 c5 c6
      (by decide) (by decide) (by decide) (by decide) d4 d5
  have d7 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c7 :=
    .initial c7 (by decide) (by decide)
  have d8 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c8 :=
    .initial c8 (by decide) (by decide)
  have d9 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c9 :=
    .initial c9 (by decide) (by decide)
  have d10 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c10 :=
    .resolve 3 c8 c9 c10
      (by decide) (by decide) (by decide) (by decide) d8 d9
  have d11 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c11 :=
    .initial c11 (by decide) (by decide)
  have d12 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c12 :=
    .resolve 8 c10 c11 c12
      (by decide) (by decide) (by decide) (by decide) d10 d11
  have d13 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c13 :=
    .resolve 7 c7 c12 c13
      (by decide) (by decide) (by decide) (by decide) d7 d12
  have d14 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c14 :=
    .resolve 11 c6 c13 c14
      (by decide) (by decide) (by decide) (by decide) d6 d13
  have d15 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c15 :=
    .initial c15 (by decide) (by decide)
  have d16 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c16 :=
    .initial c16 (by decide) (by decide)
  have d17 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c17 :=
    .resolve 1 c15 c16 c17
      (by decide) (by decide) (by decide) (by decide) d15 d16
  have d18 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c18 :=
    .initial c18 (by decide) (by decide)
  have d19 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c19 :=
    .initial c19 (by decide) (by decide)
  have d20 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c20 :=
    .resolve 5 c18 c19 c20
      (by decide) (by decide) (by decide) (by decide) d18 d19
  have d21 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c21 :=
    .resolve 10 c17 c20 c21
      (by decide) (by decide) (by decide) (by decide) d17 d20
  have d22 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c22 :=
    .initial c22 (by decide) (by decide)
  have d23 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c23 :=
    .initial c23 (by decide) (by decide)
  have d24 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c24 :=
    .resolve 5 c22 c23 c24
      (by decide) (by decide) (by decide) (by decide) d22 d23
  have d25 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c25 :=
    .initial c25 (by decide) (by decide)
  have d26 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c26 :=
    .initial c26 (by decide) (by decide)
  have d27 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c27 :=
    .resolve 1 c25 c26 c27
      (by decide) (by decide) (by decide) (by decide) d25 d26
  have d28 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c28 :=
    .resolve 10 c24 c27 c28
      (by decide) (by decide) (by decide) (by decide) d24 d27
  have d29 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c29 :=
    .resolve 9 c21 c28 c29
      (by decide) (by decide) (by decide) (by decide) d21 d28
  have d30 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c30 :=
    .resolve 0 c14 c29 c30
      (by decide) (by decide) (by decide) (by decide) d14 d29
  have d31 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c31 :=
    .initial c31 (by decide) (by decide)
  have d32 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c32 :=
    .resolve 5 c31 c23 c32
      (by decide) (by decide) (by decide) (by decide) d31 d23
  have d33 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c33 :=
    .initial c33 (by decide) (by decide)
  have d34 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c34 :=
    .resolve 1 c25 c33 c34
      (by decide) (by decide) (by decide) (by decide) d25 d33
  have d35 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c35 :=
    .resolve 10 c32 c34 c35
      (by decide) (by decide) (by decide) (by decide) d32 d34
  have d36 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c36 :=
    .initial c36 (by decide) (by decide)
  have d37 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c37 :=
    .resolve 1 c36 c16 c37
      (by decide) (by decide) (by decide) (by decide) d36 d16
  have d38 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c38 :=
    .initial c38 (by decide) (by decide)
  have d39 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c39 :=
    .resolve 5 c18 c38 c39
      (by decide) (by decide) (by decide) (by decide) d18 d38
  have d40 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c40 :=
    .resolve 10 c37 c39 c40
      (by decide) (by decide) (by decide) (by decide) d37 d39
  have d41 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c41 :=
    .resolve 9 c35 c40 c41
      (by decide) (by decide) (by decide) (by decide) d35 d40
  have d42 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c42 :=
    .initial c42 (by decide) (by decide)
  have d43 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c43 :=
    .resolve 3 c42 c2 c43
      (by decide) (by decide) (by decide) (by decide) d42 d2
  have d44 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c44 :=
    .initial c44 (by decide) (by decide)
  have d45 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c45 :=
    .resolve 8 c43 c44 c45
      (by decide) (by decide) (by decide) (by decide) d43 d44
  have d46 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c46 :=
    .resolve 7 c45 c5 c46
      (by decide) (by decide) (by decide) (by decide) d45 d5
  have d47 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c47 :=
    .initial c47 (by decide) (by decide)
  have d48 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c48 :=
    .initial c48 (by decide) (by decide)
  have d49 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c49 :=
    .resolve 3 c8 c48 c49
      (by decide) (by decide) (by decide) (by decide) d8 d48
  have d50 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c50 :=
    .resolve 8 c47 c49 c50
      (by decide) (by decide) (by decide) (by decide) d47 d49
  have d51 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c51 :=
    .resolve 7 c7 c50 c51
      (by decide) (by decide) (by decide) (by decide) d7 d50
  have d52 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c52 :=
    .resolve 11 c46 c51 c52
      (by decide) (by decide) (by decide) (by decide) d46 d51
  have d53 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c53 :=
    .resolve 0 c41 c52 c53
      (by decide) (by decide) (by decide) (by decide) d41 d52
  have d54 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c54 :=
    .resolve 4 c30 c53 c54
      (by decide) (by decide) (by decide) (by decide) d30 d53
  have d55 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c55 :=
    .initial c55 (by decide) (by decide)
  have d56 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c56 :=
    .resolve 5 c55 c19 c56
      (by decide) (by decide) (by decide) (by decide) d55 d19
  have d57 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c57 :=
    .resolve 10 c56 c34 c57
      (by decide) (by decide) (by decide) (by decide) d56 d34
  have d58 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c58 :=
    .initial c58 (by decide) (by decide)
  have d59 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c59 :=
    .resolve 5 c22 c58 c59
      (by decide) (by decide) (by decide) (by decide) d22 d58
  have d60 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c60 :=
    .resolve 10 c37 c59 c60
      (by decide) (by decide) (by decide) (by decide) d37 d59
  have d61 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c61 :=
    .resolve 9 c57 c60 c61
      (by decide) (by decide) (by decide) (by decide) d57 d60
  have d62 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c62 :=
    .initial c62 (by decide) (by decide)
  have d63 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c63 :=
    .resolve 8 c47 c3 c63
      (by decide) (by decide) (by decide) (by decide) d47 d3
  have d64 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c64 :=
    .resolve 7 c62 c63 c64
      (by decide) (by decide) (by decide) (by decide) d62 d63
  have d65 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c65 :=
    .resolve 8 c10 c44 c65
      (by decide) (by decide) (by decide) (by decide) d10 d44
  have d66 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c66 :=
    .initial c66 (by decide) (by decide)
  have d67 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c67 :=
    .resolve 7 c65 c66 c67
      (by decide) (by decide) (by decide) (by decide) d65 d66
  have d68 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c68 :=
    .resolve 11 c64 c67 c68
      (by decide) (by decide) (by decide) (by decide) d64 d67
  have d69 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c69 :=
    .resolve 0 c61 c68 c69
      (by decide) (by decide) (by decide) (by decide) d61 d68
  have d70 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c70 :=
    .resolve 8 c43 c11 c70
      (by decide) (by decide) (by decide) (by decide) d43 d11
  have d71 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c71 :=
    .resolve 7 c62 c70 c71
      (by decide) (by decide) (by decide) (by decide) d62 d70
  have d72 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c72 :=
    .resolve 8 c0 c49 c72
      (by decide) (by decide) (by decide) (by decide) d0 d49
  have d73 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c73 :=
    .resolve 7 c72 c66 c73
      (by decide) (by decide) (by decide) (by decide) d72 d66
  have d74 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c74 :=
    .resolve 11 c71 c73 c74
      (by decide) (by decide) (by decide) (by decide) d71 d73
  have d75 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c75 :=
    .resolve 5 c31 c58 c75
      (by decide) (by decide) (by decide) (by decide) d31 d58
  have d76 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c76 :=
    .resolve 10 c17 c75 c76
      (by decide) (by decide) (by decide) (by decide) d17 d75
  have d77 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c77 :=
    .resolve 5 c55 c38 c77
      (by decide) (by decide) (by decide) (by decide) d55 d38
  have d78 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c78 :=
    .resolve 10 c77 c27 c78
      (by decide) (by decide) (by decide) (by decide) d77 d27
  have d79 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c79 :=
    .resolve 9 c76 c78 c79
      (by decide) (by decide) (by decide) (by decide) d76 d78
  have d80 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c80 :=
    .resolve 0 c74 c79 c80
      (by decide) (by decide) (by decide) (by decide) d74 d79
  have d81 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c81 :=
    .resolve 4 c69 c80 c81
      (by decide) (by decide) (by decide) (by decide) d69 d80
  have d82 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c82 :=
    .resolve 6 c54 c81 c82
      (by decide) (by decide) (by decide) (by decide) d54 d81
  have d83 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c83 :=
    .initial c83 (by decide) (by decide)
  have d84 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c84 :=
    .resolve 1 c83 c33 c84
      (by decide) (by decide) (by decide) (by decide) d83 d33
  have d85 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c85 :=
    .resolve 10 c84 c20 c85
      (by decide) (by decide) (by decide) (by decide) d84 d20
  have d86 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c86 :=
    .initial c86 (by decide) (by decide)
  have d87 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c87 :=
    .resolve 1 c36 c86 c87
      (by decide) (by decide) (by decide) (by decide) d36 d86
  have d88 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c88 :=
    .resolve 10 c24 c87 c88
      (by decide) (by decide) (by decide) (by decide) d24 d87
  have d89 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c89 :=
    .resolve 9 c85 c88 c89
      (by decide) (by decide) (by decide) (by decide) d85 d88
  have d90 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c90 :=
    .initial c90 (by decide) (by decide)
  have d91 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c91 :=
    .resolve 3 c90 c9 c91
      (by decide) (by decide) (by decide) (by decide) d90 d9
  have d92 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c92 :=
    .resolve 8 c91 c44 c92
      (by decide) (by decide) (by decide) (by decide) d91 d44
  have d93 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c93 :=
    .resolve 7 c92 c5 c93
      (by decide) (by decide) (by decide) (by decide) d92 d5
  have d94 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c94 :=
    .initial c94 (by decide) (by decide)
  have d95 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c95 :=
    .resolve 3 c1 c94 c95
      (by decide) (by decide) (by decide) (by decide) d1 d94
  have d96 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c96 :=
    .resolve 8 c47 c95 c96
      (by decide) (by decide) (by decide) (by decide) d47 d95
  have d97 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c97 :=
    .resolve 7 c7 c96 c97
      (by decide) (by decide) (by decide) (by decide) d7 d96
  have d98 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c98 :=
    .resolve 11 c93 c97 c98
      (by decide) (by decide) (by decide) (by decide) d93 d97
  have d99 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c99 :=
    .resolve 0 c89 c98 c99
      (by decide) (by decide) (by decide) (by decide) d89 d98
  have d100 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c100 :=
    .resolve 3 c90 c48 c100
      (by decide) (by decide) (by decide) (by decide) d90 d48
  have d101 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c101 :=
    .resolve 8 c0 c100 c101
      (by decide) (by decide) (by decide) (by decide) d0 d100
  have d102 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c102 :=
    .resolve 7 c101 c5 c102
      (by decide) (by decide) (by decide) (by decide) d101 d5
  have d103 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c103 :=
    .resolve 3 c42 c94 c103
      (by decide) (by decide) (by decide) (by decide) d42 d94
  have d104 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c104 :=
    .resolve 8 c103 c11 c104
      (by decide) (by decide) (by decide) (by decide) d103 d11
  have d105 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c105 :=
    .resolve 7 c7 c104 c105
      (by decide) (by decide) (by decide) (by decide) d7 d104
  have d106 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c106 :=
    .resolve 11 c102 c105 c106
      (by decide) (by decide) (by decide) (by decide) d102 d105
  have d107 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c107 :=
    .resolve 1 c15 c86 c107
      (by decide) (by decide) (by decide) (by decide) d15 d86
  have d108 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c108 :=
    .resolve 10 c32 c107 c108
      (by decide) (by decide) (by decide) (by decide) d32 d107
  have d109 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c109 :=
    .resolve 1 c83 c26 c109
      (by decide) (by decide) (by decide) (by decide) d83 d26
  have d110 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c110 :=
    .resolve 10 c109 c39 c110
      (by decide) (by decide) (by decide) (by decide) d109 d39
  have d111 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c111 :=
    .resolve 9 c108 c110 c111
      (by decide) (by decide) (by decide) (by decide) d108 d110
  have d112 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c112 :=
    .resolve 0 c106 c111 c112
      (by decide) (by decide) (by decide) (by decide) d106 d111
  have d113 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c113 :=
    .resolve 4 c99 c112 c113
      (by decide) (by decide) (by decide) (by decide) d99 d112
  have d114 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c114 :=
    .resolve 8 c91 c11 c114
      (by decide) (by decide) (by decide) (by decide) d91 d11
  have d115 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c115 :=
    .resolve 7 c62 c114 c115
      (by decide) (by decide) (by decide) (by decide) d62 d114
  have d116 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c116 :=
    .resolve 8 c0 c95 c116
      (by decide) (by decide) (by decide) (by decide) d0 d95
  have d117 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c117 :=
    .resolve 7 c116 c66 c117
      (by decide) (by decide) (by decide) (by decide) d116 d66
  have d118 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c118 :=
    .resolve 11 c115 c117 c118
      (by decide) (by decide) (by decide) (by decide) d115 d117
  have d119 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c119 :=
    .resolve 10 c56 c107 c119
      (by decide) (by decide) (by decide) (by decide) d56 d107
  have d120 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c120 :=
    .resolve 10 c109 c59 c120
      (by decide) (by decide) (by decide) (by decide) d109 d59
  have d121 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c121 :=
    .resolve 9 c119 c120 c121
      (by decide) (by decide) (by decide) (by decide) d119 d120
  have d122 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c122 :=
    .resolve 0 c118 c121 c122
      (by decide) (by decide) (by decide) (by decide) d118 d121
  have d123 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c123 :=
    .resolve 10 c84 c75 c123
      (by decide) (by decide) (by decide) (by decide) d84 d75
  have d124 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c124 :=
    .resolve 10 c77 c87 c124
      (by decide) (by decide) (by decide) (by decide) d77 d87
  have d125 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c125 :=
    .resolve 9 c123 c124 c125
      (by decide) (by decide) (by decide) (by decide) d123 d124
  have d126 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c126 :=
    .resolve 8 c47 c100 c126
      (by decide) (by decide) (by decide) (by decide) d47 d100
  have d127 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c127 :=
    .resolve 7 c62 c126 c127
      (by decide) (by decide) (by decide) (by decide) d62 d126
  have d128 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c128 :=
    .resolve 8 c103 c44 c128
      (by decide) (by decide) (by decide) (by decide) d103 d44
  have d129 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c129 :=
    .resolve 7 c128 c66 c129
      (by decide) (by decide) (by decide) (by decide) d128 d66
  have d130 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c130 :=
    .resolve 11 c127 c129 c130
      (by decide) (by decide) (by decide) (by decide) d127 d129
  have d131 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c131 :=
    .resolve 0 c125 c130 c131
      (by decide) (by decide) (by decide) (by decide) d125 d130
  have d132 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c132 :=
    .resolve 4 c122 c131 c132
      (by decide) (by decide) (by decide) (by decide) d122 d131
  have d133 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c133 :=
    .resolve 6 c113 c132 c133
      (by decide) (by decide) (by decide) (by decide) d113 d132
  have d134 : WidthBoundedSetResolutionDerivation wagnerM8OddTseitinCNF 5 c134 :=
    .resolve 2 c82 c133 c134
      (by decide) (by decide) (by decide) (by decide) d82 d133
  exact d134

theorem wagner_m8_width_five_certificate_unsat :
    ¬ ∃ assignment,
      evalCNF assignment wagnerM8OddTseitinCNF = true :=
  width_bounded_set_resolution_refutation_unsat wagnerM8OddTseitinCNF 5
    wagner_m8_width_five_certificate

end AlexandriaComplexity
