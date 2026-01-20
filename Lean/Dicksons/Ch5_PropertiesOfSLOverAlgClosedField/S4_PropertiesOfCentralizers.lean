import Dicksons.Ch5_PropertiesOfSLOverAlgClosedField.S3_JordanNormalFormOfSL

set_option autoImplicit false
set_option linter.style.longLine true

open Matrix MatrixGroups Subgroup Pointwise

open SpecialMatrices SpecialSubgroups

universe u

variable
  {F : Type u} [Field F]
  (n : Type u) [Fintype n]
  (R : Type u) [CommRing R]
  {G : Type u} [Group G]

/--
The centralizer of `s σ` for `σ ≠ 0` is exactly `S F ⊔ Z F`
-/
theorem centralizer_s_eq_SZ {σ : F} (hσ : σ ≠ 0) : centralizer { s σ } = SZ F := by
  ext x
  constructor
  · intro hx
    simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq] at hx
    rw [SpecialLinearGroup.fin_two_ext_iff] at hx
    simp only [s, Fin.isValue, SpecialLinearGroup.coe_mul, cons_mul, Nat.succ_eq_add_one,
      Nat.reduceAdd, empty_mul, Equiv.symm_apply_apply, of_apply, cons_val', cons_val_fin_one,
      cons_val_zero, cons_val_one] at hx
    obtain ⟨top_right, -, bottom_left, -⟩ := hx
    rcases get_entries x with ⟨α, β, γ, δ, hα, hβ, -, hδ, x_eq⟩
    simp only [x_eq, Fin.isValue, vecMul_cons, head_cons, one_smul, tail_cons, zero_smul,
      empty_vecMul, add_zero, Pi.add_apply, cons_val_zero, Pi.zero_apply, cons_mul,
      Nat.succ_eq_add_one, Nat.reduceAdd, smul_cons, smul_eq_mul, mul_one, mul_zero, smul_empty,
      add_cons, zero_add, empty_add_empty, empty_mul, Equiv.symm_apply_apply, of_apply, cons_val',
      cons_val_fin_one, left_eq_add, mul_eq_zero, hσ, or_false,
      cons_val_one] at top_right bottom_left
    rw [add_comm γ, add_left_inj, mul_comm δ, mul_eq_mul_left_iff,
      or_iff_not_imp_right] at bottom_left
    specialize bottom_left hσ
    simp only [SZ, mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_union, Set.mem_setOf_eq]
    /- is a shear matrix if diagonal entries are equal and top right entry is zero -/
    rw [← SpecialLinearGroup.fin_two_shear_iff]
    constructor
    /- diagonal entries are equal -/
    · rw [← hα, ← hδ, bottom_left]
    /- top right entry is zero -/
    · rw [← hβ, top_right]
  · rintro (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
    repeat
    rw [mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    rw [hy]
    simp [add_comm]


lemma Field.self_eq_inv_iff (x : F) (x_ne_zero : x ≠ 0) : x = x⁻¹ ↔ x = 1 ∨ x = - 1 := by
  rw [← sq_eq_one_iff, sq, (mul_eq_one_iff_eq_inv₀ x_ne_zero)]

lemma Units.val_neg_one : ((-1 : Fˣ) : F) = -1 := by simp only [Units.val_neg, val_one]

lemma Units.val_eq_neg_one (x : Fˣ) : (x : F) = -1 ↔ x = (-1 : Fˣ) := by
  rw [← Units.val_neg_one, val_inj]

/--
The centralizer of `d δ` for `δ ≠ 1` is exactly `D F`
-/
lemma centralizer_d_eq_D (δ : Fˣ) (δ_ne_one : δ ≠ 1) (δ_ne_neg_one : δ ≠ -1) :
  centralizer {d δ} = D F := by
  ext x
  constructor
  · intro hx
    simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq] at hx
    rcases get_entries x with ⟨a, b, c, d, _ha, hb', hc', _hd, x_eq⟩
    simp only [SpecialMatrices.d, SpecialLinearGroup.fin_two_ext_iff, Fin.isValue,
      SpecialLinearGroup.coe_mul, x_eq, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
      head_cons, smul_cons, smul_eq_mul, smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero,
      zero_add, empty_mul, Equiv.symm_apply_apply, of_apply, cons_val', cons_val_zero,
      cons_val_fin_one, mul_zero, add_cons, empty_add_empty, cons_val_one] at hx
    obtain ⟨-, hb, hc, -⟩ := hx
    have δ_ne_zero : (δ : F) ≠ 0 := Units.ne_zero δ
    have δ_ne_δ_inv : (δ : F) ≠ δ⁻¹ := by
      intro h
      rw [Units.val_inj] at h
      rw [← mul_eq_one_iff_eq_inv] at h
      suffices δ = 1 ∨ δ = -1 by
        rcases this <;> contradiction
      refine Units.eq_or_eq_neg_of_sq_eq_sq δ 1 ?_
      rwa [one_pow, sq]
    rw [mul_comm, mul_eq_mul_left_iff] at hb hc
    have not_eq_inv : ¬ (δ : F)⁻¹ = (δ : F) := by
      norm_cast
      exact fun a ↦ δ_ne_δ_inv (congrArg Units.val (id (Eq.symm a)))
    replace hb : b = 0 := Or.resolve_left hb (Ne.symm not_eq_inv)
    replace hc : c = 0 := Or.resolve_left hc not_eq_inv
    rw [mem_D_iff, ← SpecialLinearGroup.fin_two_diagonal_iff]
    simp [hb, hc, ← hb', ← hc']
  · rintro ⟨δ', rfl⟩
    simp [mem_centralizer_iff, mul_comm]

lemma centralizer_d_eq_D' (δ : Fˣ) (hd: d δ ∉ center SL(2,F)) : centralizer {d δ} = D F := by
  simp [center_SL2_eq_Z, ← ne_eq] at hd
  apply centralizer_d_eq_D δ
  · rintro rfl
    simp at hd
  · rintro rfl
    simp at hd

open MulAction MulAut

lemma centralizer_neg_eq_centralizer {x : SL(2,F)} : centralizer {x} = centralizer {-x} := by
  ext; constructor <;> simp [mem_centralizer_iff_commutator_eq_one]

/--
Conjugate elements have conjugate centralizers.
-/
lemma conjugate_centralizers_of_IsConj  (a b : G) (hab : IsConj a b) :
  ∃ x : G, conj x • (centralizer { a }) = centralizer { b } := by
  rw [isConj_iff] at hab
  obtain ⟨x, hc⟩ := hab
  use x
  ext y
  simp only [conj, MonoidHom.coe_mk, OneHom.coe_mk, centralizer, mem_mk, Submonoid.mem_mk,
    Subsemigroup.mem_mk]
  constructor
  · rintro ⟨y', y'_in_centralizer, hy'⟩
    simp only [MulDistribMulAction.toMonoidEnd_apply, MulDistribMulAction.toMonoidHom_apply,
      MulAut.smul_def, MulEquiv.coe_mk, Equiv.coe_fn_mk, coe_set_mk, Submonoid.coe_set_mk,
      Subsemigroup.coe_set_mk] at hy' y'_in_centralizer ⊢
    rw [Set.mem_centralizer_iff]
    rintro m ⟨rfl⟩
    have : a * y' = y' * a := y'_in_centralizer a rfl
    rw [← hy', ← hc]
    group
    rw [mul_assoc x a, this]
    group
  · intro hy
    simp only [Set.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq] at hy
    have : y = b * y * b⁻¹ := by rw [hy]; group
    simp only [← hc, _root_.mul_inv_rev, inv_inv] at this hy
    use a * x⁻¹ * y * x * a⁻¹
    split_ands
    · simp only [coe_set_mk, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk]
      rw [Set.mem_centralizer_iff]
      simp_rw [Set.mem_singleton_iff, forall_eq, inv_mul_cancel_right]
      nth_rewrite 1 [← mul_one a, ← inv_mul_cancel x]
      have helper: a * (x⁻¹ * x) * (a * x⁻¹ * y * x * a⁻¹) =
        a * x⁻¹ * (x * a * x⁻¹ * y * x * a⁻¹) := by group
      rw [helper, hy]
      group
    · simp
      group at hy ⊢
      rw [hy]
      group

lemma MulAut.conj_smul_symm {G : Type*} [Group G] (H K : Subgroup G) (c : G)
 (h : conj c • H = K) : ∃ c' : G, conj c' • K = H := ⟨c⁻¹, by simp [← h]⟩

/--
The centraliser of a non-central element in `SL(2,F)` over an algebraically closed field `F`
is abelian.
-/
lemma IsMulCommutative_centralizer_of_not_mem_center [IsAlgClosed F] [DecidableEq F] (x : SL(2,F))
  (hx : x ∉ center SL(2,F)) : IsMulCommutative (centralizer { x }) := by
  rcases SL2_IsConj_d_or_IsConj_s_or_IsConj_neg_s_of_AlgClosed x with
    (⟨δ, x_IsConj_d⟩ | ⟨σ, x_IsConj_s⟩ | ⟨σ, x_IsConj_neg_s⟩ )
  · obtain ⟨x, centralizer_x_eq⟩ := conjugate_centralizers_of_IsConj (d δ) x x_IsConj_d
    have δ_ne_one : δ ≠ 1 := by
      rintro rfl
      simp only [d_one_eq_one, isConj_iff, mul_one, mul_inv_cancel, exists_const] at x_IsConj_d
      rw [← x_IsConj_d, center_SL2_eq_Z] at hx
      simp at hx
    have δ_ne_neg_one : δ ≠ -1 := by
      rintro rfl
      simp only [d_neg_one_eq_neg_one, isConj_iff, mul_neg, mul_one, neg_mul, mul_inv_cancel,
        exists_const] at x_IsConj_d
      rw [← x_IsConj_d, center_SL2_eq_Z] at hx
      simp at hx
    rw [← centralizer_x_eq, centralizer_d_eq_D _ δ_ne_one δ_ne_neg_one]
    exact map_isMulCommutative _ _
  · obtain ⟨x, centralizer_S_eq⟩ := conjugate_centralizers_of_IsConj (s σ) x x_IsConj_s
    have σ_ne_zero : σ ≠ 0 := by
      rintro rfl
      simp only [s_zero_eq_one, isConj_iff, mul_one, mul_inv_cancel, exists_const] at x_IsConj_s
      rw [← x_IsConj_s, center_SL2_eq_Z] at hx
      simp at hx
    rw [← centralizer_S_eq, centralizer_s_eq_SZ σ_ne_zero]
    exact map_isMulCommutative _ _
  · obtain ⟨x, centralizer_S_eq⟩ := conjugate_centralizers_of_IsConj (-s σ) x x_IsConj_neg_s
    have σ_ne_zero : σ ≠ 0 := by
      rintro rfl
      simp only [s_zero_eq_one, isConj_iff, mul_neg, mul_one, neg_mul, mul_inv_cancel,
        exists_const] at x_IsConj_neg_s
      rw [← x_IsConj_neg_s, center_SL2_eq_Z] at hx
      simp at hx
    rw [← centralizer_S_eq,  ← centralizer_neg_eq_centralizer, centralizer_s_eq_SZ σ_ne_zero]
    exact map_isMulCommutative _ _
