import Mathlib.Algebra.Polynomial.Degree.Operations

open scoped Polynomial

variable {R : Type*} [CommRing R]

#check @Polynomial.degree_lt_wf R _
#check WellFounded.min
