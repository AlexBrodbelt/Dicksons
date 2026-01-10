# Dicksons Repository - Copilot Instructions

## Repository Overview

This repository contains a formalisation of Dickson's classification theorem for finite subgroups of PGL(2,F) over algebraically closed fields in the Lean theorem prover. The classification divides finite subgroups into several families based on the relationship between the group order and the characteristic of the field.

**Project Type**: Mathematical theorem proving + Website generation  
**Primary Language**: Lean 4 (formal proof)  
**Supporting Languages**: Ruby/Jekyll  
**Primary Dependencies**: Mathlib, Subverso, Verso

## Critical Build Requirements

### ⚠️ ALWAYS Run Cache Before Building

**MOST IMPORTANT**: Before building Lean code, you **MUST** run `lake exe cache get` to download pre-compiled mathlib binaries. Without this, building will take 1+ hours and may timeout.

```bash
cd Lean
lake exe cache get  # CRITICAL: Always run this first!
lake build          # Only after cache is downloaded
```

**Build Time**:
- With cache: ~2-5 minutes for incremental builds
- Without cache: 60+ minutes (mathlib has 1000+ files)

## Repository Structure

### Root Directory Files
```
.devcontainer/          # Docker container with elan/Lean setup
.github/
  ├── workflows/
  │   └── lean_action_ci.yml  # Main CI pipeline
  └── dependabot.yml    # Dependency update config
Lean/                   # Main Lean 4 proof code
Verso/                  # Website generation code (Lean)
site/                   # Jekyll website source
scripts/                # Build scripts
requirements.txt        # Python dependencies
README.md               # Project documentation
```

### Lean Directory (`Lean/`)
**Location**: `/Lean`  
**Purpose**: Main Lean 4 formalisation code  
**Toolchain**: `leanprover/lean4:v4.25.0-rc2`  
**Build System**: Lake (Lean's build tool)

```
Lean/
├── lakefile.toml           # Lake build configuration
├── lean-toolchain          # Specifies Lean version
├── lake-manifest.json      # Dependency lock file
├── Dicksons.lean           # Root module (imports all)
└── Dicksons/               # Source files
    ├── Ch4_PGLIsoPSLOverAlgClosedField/
    │   └── ProjectiveGeneralLinearGroup.lean  # PGL ≃ PSL isomorphism
    ├── Ch5_PropertiesOfSLOverAlgClosedField/
    │   ├── S1_SpecialMatrices.lean      # Shear, diagonal, rotation matrices
    │   ├── S2_SpecialSubgroups.lean     # Important subgroups
    │   ├── S3_JordanNormalFormOfSL.lean # Jordan normal form
    │   ├── S4_PropertiesOfCentralizers.lean
    │   └── S5_PropertiesOfNormalizers.lean
    ├── Ch6_MaximalAbelianSubgroupClassEquation/
    │   ├── S1_ElementaryAbelian.lean    # Elementary abelian groups
    │   ├── S2_A_MaximalAbelianSubgroup.lean
    │   ├── S2_B_MaximalAbelianSubgroup.lean
    │   └── S3_NoncenterClassEquation.lean
    ├── Ch7_DicksonsClassificationTheorem.lean  # Main theorem (with sorry)
    └── draft.lean
```

**Key Configuration** (`lakefile.toml`):
- Project name: `dicksons`
- Dependencies: mathlib, subverso
- Linter rules enabled: line length (100 chars), multiGoal, flexible tactics

### Verso Directory (`Verso/`)
**Location**: `/Verso`  
**Purpose**: Generate website content from Lean documentation  
**Toolchain**: `leanprover/lean4:nightly-2025-07-06` (different from main Lean!)

```
Verso/
├── lakefile.toml           # Separate Lake config
├── lean-toolchain          # Different Lean version!
├── DicksonsMain.lean       # Entry point for docs generation
├── DicksonsSite.lean       # Site content definitions
├── DicksonsSite/           # Site content modules
│   ├── Expanders.lean      # Custom expanders (e.g., Mermaid diagrams)
│   └── Main.lean
└── Berso/                  # Blog generation framework
    └── Main.lean
```

**Important**: Verso uses a **different Lean version** (nightly-2025-07-06) than the main project.

### Site Directory (`site/`)
**Location**: `/site`  
**Purpose**: Jekyll static site generation  
**Theme**: dinky (remote theme: pages-themes/dinky@v0.2.0)

```
site/
├── Gemfile                 # Ruby dependencies
├── _config.yml             # Jekyll configuration
├── _includes/              # HTML partials
├── _layouts/               # Page templates
├── _sass/                  # Stylesheets
├── _pages/                 # Verso-generated content
├── -verso-css/             # Verso-generated CSS
└── -verso-js/              # Verso-generated JS
```

## Build and Validation Workflow

### 1. Building Lean Code

```bash
cd Lean

# STEP 1: ALWAYS get cache first (critical!)
lake exe cache get

# STEP 2: Build the project
lake build

# STEP 3: Build specific module (faster)
lake build Dicksons
```

**Common Issues**:
- If `lake exe cache get` fails with network errors, the build will take 60+ minutes
- Cache downloads from `lakecache.blob.core.windows.net`
- Without cache, expect to build 1000+ mathlib files

### 2. Generating Website Content

```bash
cd Verso

# Generate documentation pages (outputs to ../site/_pages)
lake exe docs
```

**Output**: Creates markdown/HTML pages in `site/_pages/` directory

### 3. Building Jekyll Site

```bash
cd site

# Install Ruby dependencies (first time only)
bundle install

# Build site
bundle exec jekyll build --destination ../_site --baseurl "/Dicksons"

# Or serve locally for development
bundle exec jekyll serve
```

**Ruby Version**: 3.1 (as specified in CI workflow)

### 4. Compiling C++ Generation Tool

```bash
cd Generation

# Compile with OpenMP support for parallelism
g++ -O3 -fopenmp coloring-integers.cpp -o coloring-integers

# Run (no input required)
./coloring-integers
```

## Continuous Integration Pipeline

**File**: `.github/workflows/lean_action_ci.yml`  
**Triggers**: Push to `main`, pull requests to `main`, manual dispatch  
**Runner**: `ubuntu-latest`

### CI Build Steps (in order):

1. **Checkout code**
2. **Build Lean files** - Uses `leanprover/lean-action@main`
   - Runs `lake build` in `Lean/` directory
   - Includes `mk_all-check: true` to verify all imports
3. **Run Verso** - Generates documentation
   - `cd Verso && lake exe docs`
4. **Setup Ruby 3.1** - For Jekyll
   - Auto-runs `bundle install` with caching
5. **Build Jekyll site**
   - `cd site && bundle exec jekyll build`
6. **Upload Pages artifact** - For GitHub Pages deployment
7. **Clean annotations** (on push only)
   - Removes `-- ANCHOR:` and `-- ANCHOR_END:` lines from .lean files
   - Deletes Verso, site, _site directories
8. **Commit to release branch** (on push only)
   - Force-pushes cleaned code to `release` branch
9. **Deploy to GitHub Pages** (separate job)

**Important**: The CI uses the `lean-action` which automatically handles `lake exe cache get`, so cache is available in CI.

## Making Changes

### Modifying Lean Proofs

1. Edit `.lean` files in `Lean/Dicksons/`
2. Check syntax: Files should type-check in your editor (VS Code with Lean extension)
3. Build to verify: `cd Lean && lake build`
4. **Do not** remove `-- ANCHOR:` comments - they're used for documentation extraction

### Modifying Website Content

1. Edit Lean documentation in `Verso/DicksonsSite.lean` or `Verso/DicksonsSite/`
2. Regenerate: `cd Verso && lake exe docs`
3. Check output in `site/_pages/`
4. Build site: `cd site && bundle exec jekyll build`

### Modifying Jekyll Theme/Layout

1. Edit files in `site/_layouts/`, `site/_includes/`, or `site/_sass/`
2. Test locally: `cd site && bundle exec jekyll serve`
3. View at `http://localhost:4000/Dicksons/`

## Common Pitfalls and Workarounds

### 1. Long Build Times
**Problem**: `lake build` takes over an hour  
**Cause**: Forgot to run `lake exe cache get`  
**Solution**: Always run `lake exe cache get` before building

### 2. Different Lean Versions
**Problem**: Verso and main Lean code use different toolchains  
**Note**: This is intentional. Verso uses nightly-2025-07-06, main uses v4.25.0-rc2  
**Action**: Don't try to unify them; keep separate

### 3. Network Restrictions
**Problem**: `lake exe cache get` fails with "Could not resolve host"  
**Workaround**: In restricted environments, you may need to build without cache (very slow) or request access to `lakecache.blob.core.windows.net`

### 4. Jekyll Bundle Install Fails
**Problem**: `bundle install` fails in `site/` directory  
**Solution**: Ensure Ruby 3.1+ is installed. On Ubuntu: `sudo apt-get install ruby-full build-essential`

### 5. Missing `lake` Command
**Problem**: `lake: command not found`  
**Solution**: Install elan (Lean version manager):
```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

### 6. Git Ignores
**Important**: The following are git-ignored:
- `*/.lake/` - Lean build artifacts
- `.python-version` - Python version specifier
- `*/_site/` - Jekyll build output
- `*/vendor/` - Ruby vendor bundle
- `.DS_Store` - macOS metadata

## Development Tools

### Lean 4 Setup
- **Editor**: VS Code with Lean 4 extension (recommended)
- **Version Manager**: elan
- **Build Tool**: lake
- **Package Manager**: lake (uses lakefile.toml)

### Linting Rules
Configured in `Lean/lakefile.toml`:
- Unicode function arrows: `fun a ↦ b`
- No auto implicit variables
- Line length limit: 100 characters
- No multiple active goals in tactics
- No rigid tactics after flexible tactics

## Key Architectural Notes

1. **Main Theorem**: Located in `Lean/Dicksons/Ch7_DicksonsClassificationTheorem.lean`
2. **Mathlib Dependency**: Heavy use of mathlib for linear algebra and group theory
3. **Subverso**: Used for documentation generation (literate programming)
4. **Annotation System**: `-- ANCHOR:` and `-- ANCHOR_END:` mark code sections for documentation
5. **Release Branch**: The `release` branch contains cleaned code without annotations
6. **GitHub Pages**: Published from artifacts via GitHub Actions, available at `https://AlexBrodbelt.github.io/Dicksons

## Quick Reference Commands

```bash
# Full build from scratch
cd Lean && lake exe cache get && lake build

# Incremental build after changes
cd Lean && lake build

# Build single module
cd Lean && lake build Dicksons.Ch4_PGLisoPSLOverAlgClosedField.ProjectiveGeneralLinearGroup

# Generate documentation
cd Verso && lake exe docs

# Build website
cd site && bundle exec jekyll build

# Serve website locally
cd site && bundle exec jekyll serve

# Clean Lean build
cd Lean && lake clean

# Update dependencies
cd Lean && lake update
```

## Mathematical Content

### Dickson's Classification Theorem

The theorem classifies finite subgroups of SL(2,F) over algebraically closed fields:

**Class I** (characteristic coprime to group order):
- Cyclic groups
- Dihedral groups
- SL(2, F₃) - Binary tetrahedral group
- SL(2, F₅) - Binary icosahedral group
- GL(2, F₃) - Extended binary octahedral group

**Class II** (characteristic divides group order):
- Elementary abelian p-groups with normal structure
- Dihedral groups (when p = 2)
- SL(2, F_q) for finite fields
- Extensions of SL(2, F_q)

### Key Definitions

- **Special Matrices**: Shear `s(σ)`, diagonal `d(δ)`, rotation `w`
- **Elementary Abelian**: Subgroups where every non-identity element has order p
- **Maximal Abelian Subgroups**: Used in the classification structure

## Trust These Instructions

This documentation has been validated for the Dicksons project. If something doesn't work as described, verify you're running commands in the correct directory and have run prerequisites (especially `lake exe cache get`). Only search for additional information if these instructions are incomplete or produce errors you cannot resolve by following the troubleshooting steps.
