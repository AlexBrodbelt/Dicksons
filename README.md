# Dickson's Classification Theorem in Lean

A formalisation of Dickson's classification theorem for finite subgroups of SL(2,F) and PGL(2,F) over algebraically closed fields in the Lean theorem prover.

This repository aims to formalise results related to the classification of finite subgroups of special linear and projective linear groups. The classification divides finite subgroups into several families based on the relationship between the group order and the characteristic of the field.

## Mathematical Background

Dickson's classification theorem provides a complete description of finite subgroups of SL(2,F) when F is an algebraically closed field. The possible finite subgroups are:

- **Cyclic groups**
- **Dihedral groups**
- **Binary polyhedral groups** (related to the symmetry groups of Platonic solids)
- **SL(2, F_q)** and its extensions for finite fields F_q

The repository structure is as follows:
- `Lean/Dicksons`: Lean formal proofs of the results
- `Verso`: Lean code to generate the website
- `site`: A partial Jekyll website, which completed by the code in `Verso`

## Prerequisites

### For Lean Builds
- [Elan](https://github.com/leanprover/elan) - Lean version manager
  ```bash
  curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
  ```

### For Website Build
- Ruby 3.1+ with Bundler
- Jekyll (installed via Bundler)

## Build Instructions

### Building the Lean Proofs

**IMPORTANT**: Before building, you must download the pre-compiled mathlib cache to avoid
a 60+ minute build time.

```bash
cd Lean
lake exe cache get  # Download mathlib cache (required!)
lake build          # Build the project
```

For incremental builds after making changes:
```bash
cd Lean
lake build
```

### Building the Verso Documentation

Verso generates web documentation from the Lean code. It requires building the highlighted
Lean files first:

```bash
# Build highlighted Lean files
cd Lean
lake exe cache get
lake build :highlighted

# Generate documentation
cd ../Verso
lake exe docs
```

The output is written to the `site/_pages/` directory.

### Building the Jekyll Website

After generating the Verso documentation:

```bash
cd site
bundle install
bundle exec jekyll build --destination ../_site --baseurl "/DicksonsVerso"
```

For local development with live reload:
```bash
cd site
bundle exec jekyll serve
```

The site will be available at `http://localhost:4000/DicksonsVerso/`.

### Building API Documentation

To generate the full API documentation using doc-gen4:

```bash
cd Lean
lake exe cache get
../scripts/build_docs.sh
```

The documentation will be generated in `Lean/docbuild/.lake/build/doc`.

## Repository Structure

### Lean/Dicksons

The formal Lean 4 proofs are organized as follows:

- **Ch4_PGLIsoPSLOverAlgClosedField/**: Establishes the isomorphism between PGL and PSL over algebraically closed fields
  - `ProjectiveGeneralLinearGroup.lean`: Definitions and properties of PGL and PSL

- **Ch5_PropertiesOfSLOverAlgClosedField/**: Properties of SL(2,F)
  - `S1_SpecialMatrices.lean`: Special matrices (shear, diagonal, rotation)
  - `S2_SpecialSubgroups.lean`: Important subgroups
  - `S3_JordanNormalFormOfSL.lean`: Jordan normal form results
  - `S4_PropertiesOfCentralizers.lean`: Centralizer properties
  - `S5_PropertiesOfNormalizers.lean`: Normalizer properties
  - `S6_TripleTransitivity.lean` : The Projective Line and Triple transitivity

- **Ch6_MaximalAbelianSubgroupClassEquation/**: Maximal abelian subgroups
  - `S1_ElementaryAbelian.lean`: Elementary abelian groups
  - `S2_A_MaximalAbelianSubgroup.lean`: Maximal abelian subgroups (Part A)
  - `S2_B_MaximalAbelianSubgroup.lean`: Maximal abelian subgroups (Part B)
  - `S3_NoncenterClassEquation.lean`: Non-center Maximal Class Equation

- **Ch7_DicksonsClassificationTheorem.lean**: The main classification theorem

## Components of project relevant to the Bonn Winter Semester 2025 Lean Course

For a description of Mara Silge's contributions see `Project2_MaraSilge.pdf`

### Main results completed throughout the Lean Course

Using Butler's exposition as reference, the main efforts went into formalising Lemma 2.3.iv a) and b) and
formalize as many of the elements necessary to state the maximal abelian subgroup class equation which will yield the case split which will result in Dickson's Classification Theorem. 

Lemma 2.3.iv a) which states: 

If $A \in \mathfrak{M}_G$ where $\mathfrak{M}$ denotes the set of maximal abelian subgroups of a subgroup $G$ and $|A|$ then $[N_G(A) : A] \le 2$.

This formalization was completed and is `MaximalAbelianSubgroup.relIndex_normalizer_le_two` in `Ch5_PropertiesOfSLOverAlgClosedField/S2_A_MaximalAbelianSubgroup.lean` 

On the way there, the following results and definitions found in `Ch5_PropertiesOfSLOverAlgClosedField/S2_A_MaximalAbelianSubgroup.lean` were needed:


- `MaximalAbelianSubgroup.mem_iff_conj_smul_mem_MaximalAbelianSubgroupsOf_conj_smul`

- `MaximalAbelianSubgroup.mem_normalizer_iff_conj_smul_mem_conj_smul_normalizer`

- `MaximalAbelianSubgroup.normalizer_subgroupOf_MulEquiv_normalizer_conj_subgroupOf`

- `MaximalAbelianSubgroup.map_normalizer_subgroupOf_eq_normalizer_conj_subgroupOf`

- `MaximalAbelianSubgroup.eq_G_inf_D_of_le_D`

- `MaximalAbelianSubgroup.mem_normalizer_iff_conj_smul_mem_conj_smul_normalizer'`

- `MaximalAbelianSubgroup.mulEquiv_ZMod_prime_of_card_prime`

- `MaximalAbelianSubgroup.card_normalizer_D_quot_D_eq_two`

- `MaximalAbelianSubgroup.subgroupOf_normalizer_monoidHom_normalizer_inf_subgroupOf`

- `MaximalAbelianSubgroup.normalizer_inf_subgroupOf_monoidHom_quot`

- `MaximalAbelianSubgroup.quot_MonoidHom_quot_of_le_D_of`

- `MaximalAbelianSubgroup.normalizer_quot_mulEquiv_quot_of`

- `MaximalAbelianSubgroup.monoidHom_normalizer_D_quot_D`

- `MaximalAbelianSubgroup.subgroupOf_normalizer_quot_monoidHom_ZMod_two`

- `MaximalAbelianSubgroup.injective_subgroupOf_normalizer_quot_monoidHom_ZMod_two`

- `MaximalAbelianSubgroup.relIndex_MaximalAbelianSubgroupOf_normalizer_eq_relIndex_conj_MaxAbelianSubgroupOf`

- `MaximalAbelianSubgroup.relIndex_eq_one_of_card_le_two`

- `MaximalAbelianSubgroup.G_ne_center_of_two_lt_card`

- `MaximalAbelianSubgroup.relIndex_normalizer_le_two`

On the other hand, lemma 2.3.iv b) which states that if the inequality in lemma 2.3.iv a) is an equality then there exists a $y \in N_G(A) \setminus A$ such that $y x y^{-1} = x^{-1}$ for all $x \in A$ is partially formalized with many of the prerequisites completed, given it is an extension of lemma 2.3.iv a)


Furthermore, starting from previous worksto begin stating the maximal abelian class equation some further results were formalized throughout the Lean course, these are:

- Theorem 2.4.i which states that the subset $G \setminus Z$ is covered by the subsets of the form $\bigcup_{x \in G} x A^* x^{-1}$, `sdiff_center_eq_union_noncenter_C`

- Theorem 2.4.ii which states that $|\{x A^* x^{-1} \}| = |x A x^{-1}|$ which corresponds to `card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet` in `Ch6_MaximalAbelianSubgroupClassEquation/S3_NoncenterClassEquation.lean` 

- Theorem 2.4.iii which states that $|\{ x A x^{-1} \; | \; x \in G \}| = |G : N_G(A)|$ which corresponds to `card_ConjClassOf_eq_index_normalizer` in  `Ch6_MaximalAbelianSubgroupClassEquation/S3_NoncenterClassEquation.lean`

The lemmas and definitions immediately involved are also part of the formalization.


### Work still in progress

Despite a lot of the pen and paper proof having been made more precise, and having found suitable theorems in `Mathlib` which will allow the results in sight. There are still theorems which remain with sorries or not stated the correct way, namely, lemma 2.3.iv b) and the maximal abelian subgroup class equation where again I am using Butler's exposition as reference. However, a lot of the pen and paper proofs have been clarified and there is much clearer strategy towards their formalization using mathlib.


### Use of AI

Claude was used to help set up the `verso` documentation and help populate the website given previous work on the formalization, but no AI aside from use of `rw?`, `exact?`, [LeanSearch](https://leansearch.net/) and [LeanExplore](https://www.leanexplore.com/) were used to assist in the formalization of the results.

### References

- Butler, Christopher (2019). "Dickson's classification of finite subgroups of the two dimensional special linear group over an algebraically closed field"
- Dickson, L.E. (1901). "Linear Groups with an Exposition of the Galois Field Theory". Teubner, Leipzig.
- Suzuki, M. (1982). "Group Theory I". Grundlehren der mathematischen Wissenschaften, vol. 247, Springer-Verlag.
- Huppert, B. (1967). "Endliche Gruppen I". Grundlehren der mathematischen Wissenschaften, vol. 134, Springer-Verlag.
