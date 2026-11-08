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

def cubeQ3FamilyJsonSHA256 : String :=
  "5590b16b47c09fc9520e8312f5155037ccd620d666783128a15b6f5180e24d38"

def cubeQ3FormulaSHA256 : String :=
  "79301572493eb36ba7e522d29b523ad7e6724dba7de2757ef52882c501f46214"

def cubeQ3OddTseitinCNF : CNF := [
  [p 0, p 1, p 2],
  [p 0, n 1, n 2],
  [n 0, p 1, n 2],
  [n 0, n 1, p 2],
  [p 0, p 3, n 4],
  [p 0, n 3, p 4],
  [n 0, p 3, p 4],
  [n 0, n 3, n 4],
  [p 1, p 5, n 6],
  [p 1, n 5, p 6],
  [n 1, p 5, p 6],
  [n 1, n 5, n 6],
  [p 3, p 5, n 7],
  [p 3, n 5, p 7],
  [n 3, p 5, p 7],
  [n 3, n 5, n 7],
  [p 2, p 8, n 9],
  [p 2, n 8, p 9],
  [n 2, p 8, p 9],
  [n 2, n 8, n 9],
  [p 4, p 8, n 10],
  [p 4, n 8, p 10],
  [n 4, p 8, p 10],
  [n 4, n 8, n 10],
  [p 6, p 9, n 11],
  [p 6, n 9, p 11],
  [n 6, p 9, p 11],
  [n 6, n 9, n 11],
  [p 7, p 10, n 11],
  [p 7, n 10, p 11],
  [n 7, p 10, p 11],
  [n 7, n 10, n 11]
]

theorem cube_q3_width_five_certificate :
    WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 [] := by
  let c0 : Clause := [p 0, p 1, p 2]
  let c1 : Clause := [n 0, p 3, p 4]
  let c2 : Clause := [p 1, p 2, p 3, p 4]
  let c3 : Clause := [n 2, p 8, p 9]
  let c4 : Clause := [p 1, p 3, p 4, p 8, p 9]
  let c5 : Clause := [n 1, p 5, p 6]
  let c6 : Clause := [n 6, p 9, p 11]
  let c7 : Clause := [n 1, p 5, p 9, p 11]
  let c8 : Clause := [p 7, p 10, n 11]
  let c9 : Clause := [p 3, p 5, n 7]
  let c10 : Clause := [p 3, p 5, p 10, n 11]
  let c11 : Clause := [n 1, p 3, p 5, p 9, p 10]
  let c12 : Clause := [p 3, n 5, p 7]
  let c13 : Clause := [n 7, p 10, p 11]
  let c14 : Clause := [p 3, n 5, p 10, p 11]
  let c15 : Clause := [p 6, p 9, n 11]
  let c16 : Clause := [n 1, n 5, n 6]
  let c17 : Clause := [n 1, n 5, p 9, n 11]
  let c18 : Clause := [n 1, p 3, n 5, p 9, p 10]
  let c19 : Clause := [n 1, p 3, p 9, p 10]
  let c20 : Clause := [p 3, p 4, p 8, p 9, p 10]
  let c21 : Clause := [p 6, n 9, p 11]
  let c22 : Clause := [p 1, p 5, n 6]
  let c23 : Clause := [p 1, p 5, n 9, p 11]
  let c24 : Clause := [p 1, p 3, p 5, n 9, p 10]
  let c25 : Clause := [p 1, n 5, p 6]
  let c26 : Clause := [n 6, n 9, n 11]
  let c27 : Clause := [p 1, n 5, n 9, n 11]
  let c28 : Clause := [p 1, p 3, n 5, n 9, p 10]
  let c29 : Clause := [p 1, p 3, n 9, p 10]
  let c30 : Clause := [p 2, p 8, n 9]
  let c31 : Clause := [p 0, n 1, n 2]
  let c32 : Clause := [n 1, n 2, p 3, p 4]
  let c33 : Clause := [n 1, p 3, p 4, p 8, n 9]
  let c34 : Clause := [p 3, p 4, p 8, n 9, p 10]
  let c35 : Clause := [p 3, p 4, p 8, p 10]
  let c36 : Clause := [n 3, p 5, p 7]
  let c37 : Clause := [n 3, p 5, p 10, p 11]
  let c38 : Clause := [p 1, p 5, p 9, n 11]
  let c39 : Clause := [p 1, n 3, p 5, p 9, p 10]
  let c40 : Clause := [p 1, n 5, p 9, p 11]
  let c41 : Clause := [n 3, n 5, n 7]
  let c42 : Clause := [n 3, n 5, p 10, n 11]
  let c43 : Clause := [p 1, n 3, n 5, p 9, p 10]
  let c44 : Clause := [p 1, n 3, p 9, p 10]
  let c45 : Clause := [p 0, n 3, p 4]
  let c46 : Clause := [n 0, n 1, p 2]
  let c47 : Clause := [n 1, p 2, n 3, p 4]
  let c48 : Clause := [n 1, n 3, p 4, p 8, p 9]
  let c49 : Clause := [n 3, p 4, p 8, p 9, p 10]
  let c50 : Clause := [n 0, p 1, n 2]
  let c51 : Clause := [p 1, n 2, n 3, p 4]
  let c52 : Clause := [p 1, n 3, p 4, p 8, n 9]
  let c53 : Clause := [n 1, p 5, n 9, n 11]
  let c54 : Clause := [n 1, n 3, p 5, n 9, p 10]
  let c55 : Clause := [n 1, n 5, n 9, p 11]
  let c56 : Clause := [n 1, n 3, n 5, n 9, p 10]
  let c57 : Clause := [n 1, n 3, n 9, p 10]
  let c58 : Clause := [n 3, p 4, p 8, n 9, p 10]
  let c59 : Clause := [n 3, p 4, p 8, p 10]
  let c60 : Clause := [p 4, p 8, p 10]
  let c61 : Clause := [p 4, n 8, p 10]
  let c62 : Clause := [p 4, p 10]
  let c63 : Clause := [p 4, p 8, n 10]
  let c64 : Clause := [p 7, n 10, p 11]
  let c65 : Clause := [p 3, p 5, n 10, p 11]
  let c66 : Clause := [p 1, p 3, p 5, p 9, n 10]
  let c67 : Clause := [n 7, n 10, n 11]
  let c68 : Clause := [p 3, n 5, n 10, n 11]
  let c69 : Clause := [p 1, p 3, n 5, p 9, n 10]
  let c70 : Clause := [p 1, p 3, p 9, n 10]
  let c71 : Clause := [p 2, n 8, p 9]
  let c72 : Clause := [n 1, p 3, p 4, n 8, p 9]
  let c73 : Clause := [p 3, p 4, n 8, p 9, n 10]
  let c74 : Clause := [n 2, n 8, n 9]
  let c75 : Clause := [p 1, p 3, p 4, n 8, n 9]
  let c76 : Clause := [n 1, p 3, p 5, n 9, n 10]
  let c77 : Clause := [n 1, p 3, n 5, n 9, n 10]
  let c78 : Clause := [n 1, p 3, n 9, n 10]
  let c79 : Clause := [p 3, p 4, n 8, n 9, n 10]
  let c80 : Clause := [p 3, p 4, n 8, n 10]
  let c81 : Clause := [p 1, n 3, p 4, n 8, p 9]
  let c82 : Clause := [n 3, p 5, n 10, n 11]
  let c83 : Clause := [n 1, n 3, p 5, p 9, n 10]
  let c84 : Clause := [n 3, n 5, n 10, p 11]
  let c85 : Clause := [n 1, n 3, n 5, p 9, n 10]
  let c86 : Clause := [n 1, n 3, p 9, n 10]
  let c87 : Clause := [n 3, p 4, n 8, p 9, n 10]
  let c88 : Clause := [p 1, n 3, p 5, n 9, n 10]
  let c89 : Clause := [p 1, n 3, n 5, n 9, n 10]
  let c90 : Clause := [p 1, n 3, n 9, n 10]
  let c91 : Clause := [n 1, n 3, p 4, n 8, n 9]
  let c92 : Clause := [n 3, p 4, n 8, n 9, n 10]
  let c93 : Clause := [n 3, p 4, n 8, n 10]
  let c94 : Clause := [p 4, n 8, n 10]
  let c95 : Clause := [p 4, n 10]
  let c96 : Clause := [p 4]
  let c97 : Clause := [n 4, p 8, p 10]
  let c98 : Clause := [p 0, p 3, n 4]
  let c99 : Clause := [p 1, n 2, p 3, n 4]
  let c100 : Clause := [p 1, p 3, n 4, n 8, p 9]
  let c101 : Clause := [p 3, n 4, n 8, p 9, p 10]
  let c102 : Clause := [n 1, p 2, p 3, n 4]
  let c103 : Clause := [n 1, p 3, n 4, n 8, n 9]
  let c104 : Clause := [p 3, n 4, n 8, n 9, p 10]
  let c105 : Clause := [p 3, n 4, n 8, p 10]
  let c106 : Clause := [n 0, n 3, n 4]
  let c107 : Clause := [n 1, n 2, n 3, n 4]
  let c108 : Clause := [n 1, n 3, n 4, n 8, p 9]
  let c109 : Clause := [n 3, n 4, n 8, p 9, p 10]
  let c110 : Clause := [p 1, p 2, n 3, n 4]
  let c111 : Clause := [p 1, n 3, n 4, n 8, n 9]
  let c112 : Clause := [n 3, n 4, n 8, n 9, p 10]
  let c113 : Clause := [n 3, n 4, n 8, p 10]
  let c114 : Clause := [n 4, n 8, p 10]
  let c115 : Clause := [n 4, p 10]
  let c116 : Clause := [n 1, p 3, n 4, p 8, p 9]
  let c117 : Clause := [p 3, n 4, p 8, p 9, n 10]
  let c118 : Clause := [p 1, p 3, n 4, p 8, n 9]
  let c119 : Clause := [p 3, n 4, p 8, n 9, n 10]
  let c120 : Clause := [p 3, n 4, p 8, n 10]
  let c121 : Clause := [p 1, n 3, n 4, p 8, p 9]
  let c122 : Clause := [n 3, n 4, p 8, p 9, n 10]
  let c123 : Clause := [n 1, n 3, n 4, p 8, n 9]
  let c124 : Clause := [n 3, n 4, p 8, n 9, n 10]
  let c125 : Clause := [n 3, n 4, p 8, n 10]
  let c126 : Clause := [n 4, p 8, n 10]
  let c127 : Clause := [n 4, n 8, n 10]
  let c128 : Clause := [n 4, n 10]
  let c129 : Clause := [n 4]
  let c130 : Clause := []

  have d0 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c0 :=
    .initial c0 (by decide) (by decide)
  have d1 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c1 :=
    .initial c1 (by decide) (by decide)
  have d2 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c2 :=
    .resolve 0 c0 c1 c2
      (by decide) (by decide) (by decide) (by decide) d0 d1
  have d3 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c3 :=
    .initial c3 (by decide) (by decide)
  have d4 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c4 :=
    .resolve 2 c2 c3 c4
      (by decide) (by decide) (by decide) (by decide) d2 d3
  have d5 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c5 :=
    .initial c5 (by decide) (by decide)
  have d6 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c6 :=
    .initial c6 (by decide) (by decide)
  have d7 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c7 :=
    .resolve 6 c5 c6 c7
      (by decide) (by decide) (by decide) (by decide) d5 d6
  have d8 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c8 :=
    .initial c8 (by decide) (by decide)
  have d9 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c9 :=
    .initial c9 (by decide) (by decide)
  have d10 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c10 :=
    .resolve 7 c8 c9 c10
      (by decide) (by decide) (by decide) (by decide) d8 d9
  have d11 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c11 :=
    .resolve 11 c7 c10 c11
      (by decide) (by decide) (by decide) (by decide) d7 d10
  have d12 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c12 :=
    .initial c12 (by decide) (by decide)
  have d13 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c13 :=
    .initial c13 (by decide) (by decide)
  have d14 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c14 :=
    .resolve 7 c12 c13 c14
      (by decide) (by decide) (by decide) (by decide) d12 d13
  have d15 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c15 :=
    .initial c15 (by decide) (by decide)
  have d16 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c16 :=
    .initial c16 (by decide) (by decide)
  have d17 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c17 :=
    .resolve 6 c15 c16 c17
      (by decide) (by decide) (by decide) (by decide) d15 d16
  have d18 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c18 :=
    .resolve 11 c14 c17 c18
      (by decide) (by decide) (by decide) (by decide) d14 d17
  have d19 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c19 :=
    .resolve 5 c11 c18 c19
      (by decide) (by decide) (by decide) (by decide) d11 d18
  have d20 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c20 :=
    .resolve 1 c4 c19 c20
      (by decide) (by decide) (by decide) (by decide) d4 d19
  have d21 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c21 :=
    .initial c21 (by decide) (by decide)
  have d22 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c22 :=
    .initial c22 (by decide) (by decide)
  have d23 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c23 :=
    .resolve 6 c21 c22 c23
      (by decide) (by decide) (by decide) (by decide) d21 d22
  have d24 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c24 :=
    .resolve 11 c23 c10 c24
      (by decide) (by decide) (by decide) (by decide) d23 d10
  have d25 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c25 :=
    .initial c25 (by decide) (by decide)
  have d26 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c26 :=
    .initial c26 (by decide) (by decide)
  have d27 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c27 :=
    .resolve 6 c25 c26 c27
      (by decide) (by decide) (by decide) (by decide) d25 d26
  have d28 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c28 :=
    .resolve 11 c14 c27 c28
      (by decide) (by decide) (by decide) (by decide) d14 d27
  have d29 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c29 :=
    .resolve 5 c24 c28 c29
      (by decide) (by decide) (by decide) (by decide) d24 d28
  have d30 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c30 :=
    .initial c30 (by decide) (by decide)
  have d31 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c31 :=
    .initial c31 (by decide) (by decide)
  have d32 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c32 :=
    .resolve 0 c31 c1 c32
      (by decide) (by decide) (by decide) (by decide) d31 d1
  have d33 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c33 :=
    .resolve 2 c30 c32 c33
      (by decide) (by decide) (by decide) (by decide) d30 d32
  have d34 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c34 :=
    .resolve 1 c29 c33 c34
      (by decide) (by decide) (by decide) (by decide) d29 d33
  have d35 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c35 :=
    .resolve 9 c20 c34 c35
      (by decide) (by decide) (by decide) (by decide) d20 d34
  have d36 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c36 :=
    .initial c36 (by decide) (by decide)
  have d37 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c37 :=
    .resolve 7 c36 c13 c37
      (by decide) (by decide) (by decide) (by decide) d36 d13
  have d38 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c38 :=
    .resolve 6 c15 c22 c38
      (by decide) (by decide) (by decide) (by decide) d15 d22
  have d39 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c39 :=
    .resolve 11 c37 c38 c39
      (by decide) (by decide) (by decide) (by decide) d37 d38
  have d40 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c40 :=
    .resolve 6 c25 c6 c40
      (by decide) (by decide) (by decide) (by decide) d25 d6
  have d41 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c41 :=
    .initial c41 (by decide) (by decide)
  have d42 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c42 :=
    .resolve 7 c8 c41 c42
      (by decide) (by decide) (by decide) (by decide) d8 d41
  have d43 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c43 :=
    .resolve 11 c40 c42 c43
      (by decide) (by decide) (by decide) (by decide) d40 d42
  have d44 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c44 :=
    .resolve 5 c39 c43 c44
      (by decide) (by decide) (by decide) (by decide) d39 d43
  have d45 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c45 :=
    .initial c45 (by decide) (by decide)
  have d46 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c46 :=
    .initial c46 (by decide) (by decide)
  have d47 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c47 :=
    .resolve 0 c45 c46 c47
      (by decide) (by decide) (by decide) (by decide) d45 d46
  have d48 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c48 :=
    .resolve 2 c47 c3 c48
      (by decide) (by decide) (by decide) (by decide) d47 d3
  have d49 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c49 :=
    .resolve 1 c44 c48 c49
      (by decide) (by decide) (by decide) (by decide) d44 d48
  have d50 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c50 :=
    .initial c50 (by decide) (by decide)
  have d51 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c51 :=
    .resolve 0 c45 c50 c51
      (by decide) (by decide) (by decide) (by decide) d45 d50
  have d52 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c52 :=
    .resolve 2 c30 c51 c52
      (by decide) (by decide) (by decide) (by decide) d30 d51
  have d53 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c53 :=
    .resolve 6 c5 c26 c53
      (by decide) (by decide) (by decide) (by decide) d5 d26
  have d54 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c54 :=
    .resolve 11 c37 c53 c54
      (by decide) (by decide) (by decide) (by decide) d37 d53
  have d55 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c55 :=
    .resolve 6 c21 c16 c55
      (by decide) (by decide) (by decide) (by decide) d21 d16
  have d56 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c56 :=
    .resolve 11 c55 c42 c56
      (by decide) (by decide) (by decide) (by decide) d55 d42
  have d57 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c57 :=
    .resolve 5 c54 c56 c57
      (by decide) (by decide) (by decide) (by decide) d54 d56
  have d58 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c58 :=
    .resolve 1 c52 c57 c58
      (by decide) (by decide) (by decide) (by decide) d52 d57
  have d59 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c59 :=
    .resolve 9 c49 c58 c59
      (by decide) (by decide) (by decide) (by decide) d49 d58
  have d60 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c60 :=
    .resolve 3 c35 c59 c60
      (by decide) (by decide) (by decide) (by decide) d35 d59
  have d61 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c61 :=
    .initial c61 (by decide) (by decide)
  have d62 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c62 :=
    .resolve 8 c60 c61 c62
      (by decide) (by decide) (by decide) (by decide) d60 d61
  have d63 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c63 :=
    .initial c63 (by decide) (by decide)
  have d64 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c64 :=
    .initial c64 (by decide) (by decide)
  have d65 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c65 :=
    .resolve 7 c64 c9 c65
      (by decide) (by decide) (by decide) (by decide) d64 d9
  have d66 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c66 :=
    .resolve 11 c65 c38 c66
      (by decide) (by decide) (by decide) (by decide) d65 d38
  have d67 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c67 :=
    .initial c67 (by decide) (by decide)
  have d68 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c68 :=
    .resolve 7 c12 c67 c68
      (by decide) (by decide) (by decide) (by decide) d12 d67
  have d69 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c69 :=
    .resolve 11 c40 c68 c69
      (by decide) (by decide) (by decide) (by decide) d40 d68
  have d70 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c70 :=
    .resolve 5 c66 c69 c70
      (by decide) (by decide) (by decide) (by decide) d66 d69
  have d71 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c71 :=
    .initial c71 (by decide) (by decide)
  have d72 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c72 :=
    .resolve 2 c71 c32 c72
      (by decide) (by decide) (by decide) (by decide) d71 d32
  have d73 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c73 :=
    .resolve 1 c70 c72 c73
      (by decide) (by decide) (by decide) (by decide) d70 d72
  have d74 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c74 :=
    .initial c74 (by decide) (by decide)
  have d75 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c75 :=
    .resolve 2 c2 c74 c75
      (by decide) (by decide) (by decide) (by decide) d2 d74
  have d76 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c76 :=
    .resolve 11 c65 c53 c76
      (by decide) (by decide) (by decide) (by decide) d65 d53
  have d77 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c77 :=
    .resolve 11 c55 c68 c77
      (by decide) (by decide) (by decide) (by decide) d55 d68
  have d78 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c78 :=
    .resolve 5 c76 c77 c78
      (by decide) (by decide) (by decide) (by decide) d76 d77
  have d79 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c79 :=
    .resolve 1 c75 c78 c79
      (by decide) (by decide) (by decide) (by decide) d75 d78
  have d80 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c80 :=
    .resolve 9 c73 c79 c80
      (by decide) (by decide) (by decide) (by decide) d73 d79
  have d81 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c81 :=
    .resolve 2 c71 c51 c81
      (by decide) (by decide) (by decide) (by decide) d71 d51
  have d82 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c82 :=
    .resolve 7 c36 c67 c82
      (by decide) (by decide) (by decide) (by decide) d36 d67
  have d83 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c83 :=
    .resolve 11 c7 c82 c83
      (by decide) (by decide) (by decide) (by decide) d7 d82
  have d84 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c84 :=
    .resolve 7 c64 c41 c84
      (by decide) (by decide) (by decide) (by decide) d64 d41
  have d85 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c85 :=
    .resolve 11 c84 c17 c85
      (by decide) (by decide) (by decide) (by decide) d84 d17
  have d86 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c86 :=
    .resolve 5 c83 c85 c86
      (by decide) (by decide) (by decide) (by decide) d83 d85
  have d87 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c87 :=
    .resolve 1 c81 c86 c87
      (by decide) (by decide) (by decide) (by decide) d81 d86
  have d88 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c88 :=
    .resolve 11 c23 c82 c88
      (by decide) (by decide) (by decide) (by decide) d23 d82
  have d89 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c89 :=
    .resolve 11 c84 c27 c89
      (by decide) (by decide) (by decide) (by decide) d84 d27
  have d90 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c90 :=
    .resolve 5 c88 c89 c90
      (by decide) (by decide) (by decide) (by decide) d88 d89
  have d91 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c91 :=
    .resolve 2 c47 c74 c91
      (by decide) (by decide) (by decide) (by decide) d47 d74
  have d92 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c92 :=
    .resolve 1 c90 c91 c92
      (by decide) (by decide) (by decide) (by decide) d90 d91
  have d93 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c93 :=
    .resolve 9 c87 c92 c93
      (by decide) (by decide) (by decide) (by decide) d87 d92
  have d94 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c94 :=
    .resolve 3 c80 c93 c94
      (by decide) (by decide) (by decide) (by decide) d80 d93
  have d95 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c95 :=
    .resolve 8 c63 c94 c95
      (by decide) (by decide) (by decide) (by decide) d63 d94
  have d96 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c96 :=
    .resolve 10 c62 c95 c96
      (by decide) (by decide) (by decide) (by decide) d62 d95
  have d97 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c97 :=
    .initial c97 (by decide) (by decide)
  have d98 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c98 :=
    .initial c98 (by decide) (by decide)
  have d99 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c99 :=
    .resolve 0 c98 c50 c99
      (by decide) (by decide) (by decide) (by decide) d98 d50
  have d100 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c100 :=
    .resolve 2 c71 c99 c100
      (by decide) (by decide) (by decide) (by decide) d71 d99
  have d101 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c101 :=
    .resolve 1 c100 c19 c101
      (by decide) (by decide) (by decide) (by decide) d100 d19
  have d102 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c102 :=
    .resolve 0 c98 c46 c102
      (by decide) (by decide) (by decide) (by decide) d98 d46
  have d103 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c103 :=
    .resolve 2 c102 c74 c103
      (by decide) (by decide) (by decide) (by decide) d102 d74
  have d104 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c104 :=
    .resolve 1 c29 c103 c104
      (by decide) (by decide) (by decide) (by decide) d29 d103
  have d105 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c105 :=
    .resolve 9 c101 c104 c105
      (by decide) (by decide) (by decide) (by decide) d101 d104
  have d106 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c106 :=
    .initial c106 (by decide) (by decide)
  have d107 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c107 :=
    .resolve 0 c31 c106 c107
      (by decide) (by decide) (by decide) (by decide) d31 d106
  have d108 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c108 :=
    .resolve 2 c71 c107 c108
      (by decide) (by decide) (by decide) (by decide) d71 d107
  have d109 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c109 :=
    .resolve 1 c44 c108 c109
      (by decide) (by decide) (by decide) (by decide) d44 d108
  have d110 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c110 :=
    .resolve 0 c0 c106 c110
      (by decide) (by decide) (by decide) (by decide) d0 d106
  have d111 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c111 :=
    .resolve 2 c110 c74 c111
      (by decide) (by decide) (by decide) (by decide) d110 d74
  have d112 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c112 :=
    .resolve 1 c111 c57 c112
      (by decide) (by decide) (by decide) (by decide) d111 d57
  have d113 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c113 :=
    .resolve 9 c109 c112 c113
      (by decide) (by decide) (by decide) (by decide) d109 d112
  have d114 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c114 :=
    .resolve 3 c105 c113 c114
      (by decide) (by decide) (by decide) (by decide) d105 d113
  have d115 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c115 :=
    .resolve 8 c97 c114 c115
      (by decide) (by decide) (by decide) (by decide) d97 d114
  have d116 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c116 :=
    .resolve 2 c102 c3 c116
      (by decide) (by decide) (by decide) (by decide) d102 d3
  have d117 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c117 :=
    .resolve 1 c70 c116 c117
      (by decide) (by decide) (by decide) (by decide) d70 d116
  have d118 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c118 :=
    .resolve 2 c30 c99 c118
      (by decide) (by decide) (by decide) (by decide) d30 d99
  have d119 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c119 :=
    .resolve 1 c118 c78 c119
      (by decide) (by decide) (by decide) (by decide) d118 d78
  have d120 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c120 :=
    .resolve 9 c117 c119 c120
      (by decide) (by decide) (by decide) (by decide) d117 d119
  have d121 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c121 :=
    .resolve 2 c110 c3 c121
      (by decide) (by decide) (by decide) (by decide) d110 d3
  have d122 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c122 :=
    .resolve 1 c121 c86 c122
      (by decide) (by decide) (by decide) (by decide) d121 d86
  have d123 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c123 :=
    .resolve 2 c30 c107 c123
      (by decide) (by decide) (by decide) (by decide) d30 d107
  have d124 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c124 :=
    .resolve 1 c90 c123 c124
      (by decide) (by decide) (by decide) (by decide) d90 d123
  have d125 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c125 :=
    .resolve 9 c122 c124 c125
      (by decide) (by decide) (by decide) (by decide) d122 d124
  have d126 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c126 :=
    .resolve 3 c120 c125 c126
      (by decide) (by decide) (by decide) (by decide) d120 d125
  have d127 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c127 :=
    .initial c127 (by decide) (by decide)
  have d128 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c128 :=
    .resolve 8 c126 c127 c128
      (by decide) (by decide) (by decide) (by decide) d126 d127
  have d129 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c129 :=
    .resolve 10 c115 c128 c129
      (by decide) (by decide) (by decide) (by decide) d115 d128
  have d130 : WidthBoundedSetResolutionDerivation cubeQ3OddTseitinCNF 5 c130 :=
    .resolve 4 c96 c129 c130
      (by decide) (by decide) (by decide) (by decide) d96 d129
  exact d130

theorem cube_q3_width_five_certificate_unsat :
    ¬ ∃ assignment,
      evalCNF assignment cubeQ3OddTseitinCNF = true :=
  width_bounded_set_resolution_refutation_unsat cubeQ3OddTseitinCNF 5
    cube_q3_width_five_certificate

end AlexandriaComplexity
