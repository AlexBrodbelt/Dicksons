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

- **Ch6_MaximalAbelianSubgroupClassEquation/**: Maximal abelian subgroups
  - `S1_ElementaryAbelian.lean`: Elementary abelian groups
  - `S2_A_MaximalAbelianSubgroup.lean`: Maximal abelian subgroups (Part A)
  - `S2_B_MaximalAbelianSubgroup.lean`: Maximal abelian subgroups (Part B)
  - `S3_NoncenterClassEquation.lean`: Non-center Maximal Class Equation

- **Ch7_DicksonsClassificationTheorem.lean**: The main classification theorem

## References

- Dickson, L.E. (1901). "Linear Groups with an Exposition of the Galois Field Theory". Teubner, Leipzig.
- Suzuki, M. (1982). "Group Theory I". Grundlehren der mathematischen Wissenschaften, vol. 247, Springer-Verlag.
- Huppert, B. (1967). "Endliche Gruppen I". Grundlehren der mathematischen Wissenschaften, vol. 134, Springer-Verlag.
