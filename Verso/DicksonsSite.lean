/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/

import Berso.Main
import DicksonsSite.Expanders

-- This gets access to most of the blog genre
open Verso Genre Blog

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Code.External

set_option pp.rawOnError true

-- This is the source of code examples to be shown in the document. It should be relative to the
-- current Lake workspace. One good way to set up the files is in a Git repository that contains one
-- Lake package for example code and another for the docs, as sibling directories.
set_option verso.exampleProject "../Lean"

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "Dicksons"

#doc (Page) "Dickson's Classification Theorem" =>

# Overview

This repository provides a formalisation in the Lean 4 theorem prover of results related to
Dickson's classification theorem for finite subgroups of $`\text{SL}(2, F)` and
$`\text{PGL}(2, F)` over algebraically closed fields.

The classification of finite subgroups of linear groups is a classical topic in group theory,
with applications to algebraic geometry, representation theory, and number theory.
Dickson's theorem provides a complete classification of finite subgroups of $`\text{SL}(2, F)`
when $`F` is an algebraically closed field.

# Mathematical Background

## Special Linear Groups

The special linear group $`\text{SL}(n, F)` consists of all $`n \times n` matrices with
determinant 1 over the field $`F`. For $`n = 2`, this group has a rich structure that allows
for a complete classification of its finite subgroups.

## Projective Linear Groups

The projective general linear group $`\text{PGL}(n, F)` is the quotient of the general linear
group $`\text{GL}(n, F)` by its center. Similarly, the projective special linear group
$`\text{PSL}(n, F)` is the quotient of $`\text{SL}(n, F)` by its center.

Over an algebraically closed field, these projective groups are isomorphic:

```anchor PGL_iso_PSL (module := Dicksons.Ch4_PGLIsoPSLOverAlgClosedField.ProjectiveGeneralLinearGroup)
noncomputable def PGL_iso_PSL (n F : Type*) [Fintype n] [DecidableEq n] [Field F]
  [IsAlgClosed F] : PSL n F ≃* PGL n F :=
    MulEquiv.ofBijective (PSL_monoidHom_PGL n F) (Bijective_PSL_monoidHom_PGL n F)
```

## Special Matrices

We define several important families of matrices in $`\text{SL}(2, F)`:

### Shear Matrices

The shear matrix $`s(\sigma)` for $`\sigma \in F`:

```anchor SpecialMatrices.s (module := Dicksons.Ch5_PropertiesOfSLOverAlgClosedField.S1_SpecialMatrices)
def s (σ : F) : SL(2,F) :=
  ⟨!![1, 0; σ, 1], by simp⟩
```

These matrices satisfy $`s(\sigma) \cdot s(\mu) = s(\sigma + \mu)`.

### Diagonal Matrices

The diagonal matrix $`d(\delta)` for $`\delta \in F^\times`:

```anchor SpecialMatrices.d (module := Dicksons.Ch5_PropertiesOfSLOverAlgClosedField.S1_SpecialMatrices)
def d (δ : Fˣ) : SL(2, F) :=
  ⟨!![(δ : F), 0; 0 , δ⁻¹], by norm_num⟩
```

These matrices satisfy $`d(\delta) \cdot d(\rho) = d(\delta \rho)`.

### Rotation Matrix

The rotation matrix $`w`:

```anchor SpecialMatrices.w (module := Dicksons.Ch5_PropertiesOfSLOverAlgClosedField.S1_SpecialMatrices)
def w : SL(2, F) :=
  ⟨!![0,1;-1,0], by norm_num⟩
```

This satisfies $`w^2 = -1`.

## Elementary Abelian Subgroups

A subgroup $`H` is called elementary abelian of exponent $`p` if it is abelian and every
non-identity element has order $`p`:

```anchor IsElementaryAbelian (module := Dicksons.Ch6_MaximalAbelianSubgroupClassEquation.S1_ElementaryAbelian)
def IsElementaryAbelian {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) : Prop :=
  IsMulCommutative H ∧ ∀ h : H, h ≠ 1 → orderOf h = p
```

# Dickson's Classification Theorem

## Main Theorem Structure

The classification divides finite subgroups of $`\text{SL}(2, F)` into several cases based on
the relationship between the group and its Sylow $`p`-subgroups, where $`p` is the
characteristic of the field.

## Classification for Characteristic Coprime Groups

When the order of $`G` is coprime to the characteristic $`p` of the field:

```anchor dicksons_classification_theorem_class_I (module := Dicksons.Ch7_DicksonsClassificationTheorem)
theorem dicksons_classification_theorem_class_I {F : Type*} [Field F] [IsAlgClosed F]
  {p : ℕ} [CharP F p] (hp : Prime p) (G : Subgroup (SL(2,F)))  [Finite G]
  (hp' : p = 0 ∨ Nat.Coprime (Nat.card G) p) :
  IsCyclic G ∨
  Isomorphic G (DihedralGroup n)
  ∨
  Isomorphic G SL(2, ZMod 3)
  ∨
  Isomorphic G SL(2, ZMod 5)
  ∨
  Isomorphic G (GL (Fin 2) (ZMod 3))
  := by sorry
```

## Classification for Characteristic Dividing Groups

When the characteristic $`p` divides the order of the group:

```anchor dicksons_classification_theorem_class_II (module := Dicksons.Ch7_DicksonsClassificationTheorem)
theorem dicksons_classification_theorem_class_II {F : Type*} [Field F] [IsAlgClosed F]{p : ℕ}
  [Fact (Nat.Prime p)] [CharP F p] (G : Subgroup (SL(2,F))) [Finite G] (hp : p ∣ Nat.card G) :
  ∃ Q : Subgroup SL(2,F), IsElementaryAbelian p Q ∧ Normal Q ∧ Isomorphic G Q
  ∨
  (p = 2 ∧ ∃ n : ℕ, Odd n ∧ Isomorphic G (DihedralGroup n))
  ∨
  Isomorphic G SL(2, ZMod 5)
  ∨
  ∃ k : ℕ+, Isomorphic G SL(2, GaloisField p k)
  ∨
  ∃ k : ℕ+, ∃ x : GaloisField p (2* k), orderOf x^2 = p^(k : ℕ) ∧
    ∃ φ : G ≃* SL(2, GaloisField p k), True
  := by sorry
```

## Classification for PGL₂

The classification extends to finite subgroups of $`\text{PGL}(2, \overline{\mathbb{F}_p})`:

```anchor FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod (module := Dicksons.Ch7_DicksonsClassificationTheorem)
theorem FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod {p : ℕ} [Fact (Nat.Prime p)] (𝕂 : Type*)
  [Field 𝕂] [CharP 𝕂 p] [Finite 𝕂]
  (G : Subgroup (PGL (Fin 2) (AlgebraicClosure (ZMod p)))) [hG : Finite G] :
  IsCyclic G
  ∨
  ∃ n, Isomorphic G (DihedralGroup n)
  ∨
  Isomorphic G (alternatingGroup (Fin 4))
  ∨
  Isomorphic G (Equiv.Perm (Fin 5))
  ∨
  Isomorphic G (alternatingGroup (Fin 5))
  ∨
  Isomorphic G (PSL (Fin 2) (𝕂))
  ∨
  Isomorphic G (PGL (Fin 2) (𝕂)) := by
    sorry
```

# Repository Structure

The repository is organised as follows:

: `Lean/Dicksons`

  The formal Lean 4 proofs, including:
  - `Ch4_PGLIsoPSLOverAlgClosedField/`: Isomorphism between PGL and PSL over algebraically closed fields
  - `Ch5_PropertiesOfSLOverAlgClosedField/`: Properties of SL₂ including special matrices and subgroups
  - `Ch6_MaximalAbelianSubgroupClassEquation/`: Maximal abelian subgroups and class equations
  - `Ch7_DicksonsClassificationTheorem.lean`: The main classification theorem

: `Verso`

  Lean code for generating this documentation website using the Verso framework.

: `site`

  Jekyll website source files, completed by the Verso-generated content.

# References

- Dickson, L.E. (1901). "Linear Groups with an Exposition of the Galois Field Theory".
  *Teubner*, Leipzig.
- Suzuki, M. (1982). "Group Theory I". *Grundlehren der mathematischen Wissenschaften*,
  vol. 247, Springer-Verlag.
- Huppert, B. (1967). "Endliche Gruppen I". *Grundlehren der mathematischen Wissenschaften*,
  vol. 134, Springer-Verlag.
