/-
Copyright (c) 2026 Sanghyeok Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sanghyeok Park
-/
module

public import Mathlib.Logic.Relation.GroebnerBasisCriterion

/-!
# Buchberger criterion

This file starts the formalization of Becker--Weispfenning--Kredel,
Section 5.3.

The first result below is the reduction-theoretic core of Lemma 5.44:
to prove that `G` is a Gröbner basis, it suffices to show that every
one-step peak has reducts whose difference reduces to zero.
-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial
open scoped MonomialOrder Reduction

variable {σ : Type*} (m : MonomialOrder σ)

section sPolynomial

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/--
Becker--Weispfenning--Kredel, Exercise 5.47(iii).

If the leading term of `g` divides the leading term of `f`, then
`C (m.leadingCoeff g) * f` top-reduces modulo `g` to the S-polynomial
of `f` and `g`.
-/
theorem topReduces_C_leadingCoeff_mul_to_sPolynomial
    {f g : MvPolynomial σ R}
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    (hdiv : m.degree g ≤ m.degree f) :
    m.TopReduces g
      (C (m.leadingCoeff g) * f)
      (m.sPolynomial f g) := by
  have hLCf : m.leadingCoeff f ≠ 0 :=
    m.leadingCoeff_ne_zero_iff.mpr hf
  have hLCg : m.leadingCoeff g ≠ 0 :=
    m.leadingCoeff_ne_zero_iff.mpr hg
  have hCg : (C (m.leadingCoeff g) : MvPolynomial σ R) ≠ 0 := by
    simpa using hLCg
  have hdeg :
      m.degree (C (m.leadingCoeff g) * f) = m.degree f := by
    rw [m.degree_mul hCg hf, m.degree_C, zero_add]
  rw [TopReduces, ReducesToBy, hdeg]
  refine
    ⟨hg, ?_, m.degree f - m.degree g, ?_,
      m.leadingCoeff f, ?_, ?_⟩
  · have hprod : (C (m.leadingCoeff g) * f : MvPolynomial σ R) ≠ 0 :=
      mul_ne_zero hCg hf
    simpa [hdeg] using
      m.degree_mem_support hprod
  · exact tsub_add_cancel_of_le hdiv
  · rw [← zero_add (m.degree f), ← m.degree_C (m.leadingCoeff g),
      coeff_mul_of_degree_add (m := m), m.leadingCoeff_C]
    exact mul_comm (m.leadingCoeff f) (m.leadingCoeff g)
  · rw [sPolynomial, tsub_eq_zero_of_le hdiv, monomial_zero']

/-- Multiplication by a nonzero monomial preserves one-step reduction modulo a set. -/
theorem monomial_mul_reducesToSet
    (u : σ →₀ ℕ) {c : R} (hc : c ≠ 0)
    (P : Set (MvPolynomial σ R))
    {f g : MvPolynomial σ R}
    (h : f ⟶[m, P] g) :
    monomial u c * f ⟶[m, P] monomial u c * g := by
  rcases h with ⟨p, hpP, t, hp, ht, s, hs, a, ha, hg⟩
  refine ⟨p, hpP, u + t, hp, ?_, u + s, ?_, c * a, ?_, ?_⟩
  · rw [MvPolynomial.mem_support_iff] at ht ⊢
    simpa only [coeff_monomial_mul] using mul_ne_zero hc ht
  · simp only [add_assoc, hs]
  · have hcoeff :
        (monomial u c * f).coeff (u + t) = c * f.coeff t := by
      simp only [coeff_monomial_mul]
    rw [hcoeff, ← ha]
    ring
  · calc
      monomial u c * g
          = monomial u c * (f - monomial s a * p) := by
              rw [hg]
      _ = monomial u c * f - (monomial u c * monomial s a) * p := by
              ring
      _ = monomial u c * f - monomial (u + s) (c * a) * p := by
              rw [monomial_mul]

/-- Multiplication by a monomial preserves finite reduction modulo a set. -/
theorem monomial_mul_reflTransGen
    (u : σ →₀ ℕ) (c : R)
    (P : Set (MvPolynomial σ R))
    {f g : MvPolynomial σ R}
    (h : f ⟶*[m, P] g) :
    monomial u c * f ⟶*[m, P] monomial u c * g := by
  by_cases hc : c = 0
  · subst c
    simpa using
      (Relation.ReflTransGen.refl :
        (0 : MvPolynomial σ R) ⟶*[m, P] 0)
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (monomial_mul_reducesToSet m u hc P hstep)

/-- A monomial multiple of a member of `P` reduces to zero in one step,
when its leading coefficient is nonzero. -/
theorem monomial_mul_mem_reducesTo_zero
    (P : Set (MvPolynomial σ R))
    {p : MvPolynomial σ R} (hpP : p ∈ P) (hp : p ≠ 0)
    (s : σ →₀ ℕ) {c : R}
    (hc : c * m.leadingCoeff p ≠ 0) :
    monomial s c * p ⟶[m, P] 0 := by
  refine ⟨p, hpP, s + m.degree p, hp, ?_, s, rfl, c, ?_, ?_⟩
  · rw [MvPolynomial.mem_support_iff]
    rw [coeff_monomial_mul]
    simpa using hc
  · rw [coeff_monomial_mul]
    rfl
  · simp

end sPolynomial

namespace IsGroebner

section CommRing

variable {R : Type*} [CommRing R]

/--
Reduction-theoretic core of Becker--Weispfenning--Kredel, Lemma 5.44.

If every local peak `f ⟶ f₁`, `f ⟶ f₂` has the property that
`f₂ - f₁` reduces to zero, then reduction modulo `G` is locally confluent;
by Theorem 5.35, `G` is a Gröbner basis.
-/
theorem of_localPeak_sub_reflTransGen_zero
    (G : Set (MvPolynomial σ R))
    (hG₀ : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (hpeak :
      ∀ ⦃f f₁ f₂ : MvPolynomial σ R⦄,
        f ⟶[m, G] f₁ →
          f ⟶[m, G] f₂ →
            f₂ - f₁ ⟶*[m, G] 0) :
    m.IsGroebner G := by
  apply (iff_locallyConfluent (m := m) G hG₀).2
  intro f f₁ f₂ hf₁ hf₂
  have hsub : f₂ - f₁ ⟶*[m, G] 0 :=
    hpeak hf₁ hf₂
  rcases m.join_of_sub_reflTransGen_zero G hG₀ f₂ f₁ hsub with
    ⟨d, hf₂d, hf₁d⟩
  exact ⟨d, hf₁d, hf₂d⟩

/--
Theorem 5.48, forward implication.

If `G` is a Gröbner basis, then every S-polynomial of two elements of `G`
reduces to zero modulo `G`.
-/
theorem sPolynomial_reflTransGen_zero
    (G : Set (MvPolynomial σ R))
    (hG₀ : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (hG : m.IsGroebner G)
    {g₁ g₂ : MvPolynomial σ R}
    (hg₁ : g₁ ∈ G)
    (hg₂ : g₂ ∈ G) :
    m.sPolynomial g₁ g₂ ⟶*[m, G] 0 := by
  have hred :
      ∀ f : MvPolynomial σ R,
        f ∈ Ideal.span G →
          f ⟶*[m, G] 0 :=
    (iff_idealElements_reduceTo_zero m G hG₀).1 hG
  exact hred (m.sPolynomial g₁ g₂)
    (m.sPolynomial_mem_ideal
      (Ideal.subset_span hg₁)
      (Ideal.subset_span hg₂))

/--
Theorem 5.48, forward implication in normal-form form.

If `G` is a Gröbner basis, then every normal form of an S-polynomial of two
elements of `G` is zero.
-/
theorem normalForm_sPolynomial_eq_zero
    (G : Set (MvPolynomial σ R))
    (hG₀ : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (hG : m.IsGroebner G)
    {g₁ g₂ h : MvPolynomial σ R}
    (hg₁ : g₁ ∈ G)
    (hg₂ : g₂ ∈ G)
    (hnf : Relation.IsNormalFormOf
      (m.ReducesToSet G) (m.sPolynomial g₁ g₂) h) :
    h = 0 := by
  have hunf :
      Relation.UniqueNormalForms (m.ReducesToSet G) :=
    (iff_uniqueNormalForms (m := m) G hG₀).1 hG
  exact hunf
    hnf.1
    (sPolynomial_reflTransGen_zero m G hG₀ hG hg₁ hg₂)
    hnf.2
    (zero_isNormalForm m G)

/--
Theorem 5.48, implication `(ii) → (iii)`.

If every normal form of each S-polynomial of pairs from `G` is zero, then
each such S-polynomial reduces to zero.
-/
theorem sPolynomial_reflTransGen_zero_of_normalForms_eq_zero
    (G : Set (MvPolynomial σ R))
    (hnf_zero :
      ∀ {g₁ g₂ h : MvPolynomial σ R},
        g₁ ∈ G →
          g₂ ∈ G →
            Relation.IsNormalFormOf
              (m.ReducesToSet G) (m.sPolynomial g₁ g₂) h →
              h = 0)
    {g₁ g₂ : MvPolynomial σ R}
    (hg₁ : g₁ ∈ G)
    (hg₂ : g₂ ∈ G) :
    m.sPolynomial g₁ g₂ ⟶*[m, G] 0 := by
  rcases
    Relation.exists_normalFormOf_of_wellFounded_flip
      (ReducesToSet.wellFounded m G)
      (m.sPolynomial g₁ g₂)
    with ⟨h, hnf⟩
  have hzero : h = 0 :=
    hnf_zero hg₁ hg₂ hnf
  simpa [hzero] using hnf.1

/--
Theorem 5.48, implication `(iii) → (i)`.

If every S-polynomial of two elements of `G` reduces to zero modulo `G`,
then `G` is a Gröbner basis.
-/
theorem of_sPolynomial_reflTransGen_zero
    [NoZeroDivisors R]
    (G : Set (MvPolynomial σ R))
    (hG₀ : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (hspol :
      ∀ g₁ ∈ G, ∀ g₂ ∈ G,
        m.sPolynomial g₁ g₂ ⟶*[m, G] 0) :
    m.IsGroebner G := by
  classical
  apply of_localPeak_sub_reflTransGen_zero m G hG₀
  intro f f₁ f₂ hf₁ hf₂
  rcases hf₁ with ⟨p₁, hp₁G, t₁, hp₁, ht₁, s₁, hs₁, c₁, hc₁, hf₁_eq⟩
  rcases hf₂ with ⟨p₂, hp₂G, t₂, hp₂, ht₂, s₂, hs₂, c₂, hc₂, hf₂_eq⟩
  let q₁ : MvPolynomial σ R := monomial s₁ c₁ * p₁
  let q₂ : MvPolynomial σ R := monomial s₂ c₂ * p₂
  have hdiff : f₂ - f₁ = q₁ - q₂ := by
    simp only [q₁, q₂, hf₁_eq, hf₂_eq]
    ring
  rw [hdiff]
  have hc₁_ne_prod : c₁ * m.leadingCoeff p₁ ≠ 0 := by
    rw [hc₁]
    exact MvPolynomial.mem_support_iff.mp ht₁
  have hc₂_ne_prod : c₂ * m.leadingCoeff p₂ ≠ 0 := by
    rw [hc₂]
    exact MvPolynomial.mem_support_iff.mp ht₂
  have hc₁_ne : c₁ ≠ 0 := by
    intro hc
    exact hc₁_ne_prod (by simp [hc])
  have hc₂_ne : c₂ ≠ 0 := by
    intro hc
    exact hc₂_ne_prod (by simp [hc])
  have hq₁_degree : m.degree q₁ = t₁ := by
    unfold q₁
    rw [m.degree_mul_of_mul_leadingCoeff_ne_zero]
    · rw [m.degree_monomial, if_neg hc₁_ne, hs₁]
    · simpa using hc₁_ne_prod
  have hq₂_degree : m.degree q₂ = t₂ := by
    unfold q₂
    rw [m.degree_mul_of_mul_leadingCoeff_ne_zero]
    · rw [m.degree_monomial, if_neg hc₂_ne, hs₂]
    · simpa using hc₂_ne_prod
  have hq₁_coeff : q₁.coeff t₁ = c₁ * m.leadingCoeff p₁ := by
    unfold q₁
    rw [← hs₁, coeff_monomial_mul]
    rfl
  have hq₂_coeff : q₂.coeff t₂ = c₂ * m.leadingCoeff p₂ := by
    unfold q₂
    rw [← hs₂, coeff_monomial_mul]
    rfl
  by_cases ht : t₁ = t₂
  · have hs₂t : s₂ + m.degree p₂ = t₁ := by
      simpa [ht] using hs₂
    have hc₂t : c₂ * m.leadingCoeff p₂ = coeff t₁ f := by
      simpa [ht] using hc₂
    have hp₂_unit : IsUnit (m.leadingCoeff p₂) := by
      rcases hG₀ p₂ hp₂G with hunit | hp₂_zero
      · exact hunit
      · exact False.elim (hp₂ hp₂_zero)
    rcases hp₂_unit with ⟨u₂, hu₂⟩
    let l : σ →₀ ℕ := m.degree p₁ ⊔ m.degree p₂
    let v : σ →₀ ℕ := t₁ - l
    let k : R := c₁ * ↑u₂⁻¹
    have hle₁t : m.degree p₁ ≤ t₁ := by
      rw [← hs₁]
      exact self_le_add_left _ _
    have hle₂t : m.degree p₂ ≤ t₁ := by
      rw [← hs₂t]
      exact self_le_add_left _ _
    have hv₁ : v + (l - m.degree p₁) = s₁ := by
      unfold v l
      ext x
      have hsx : s₁ x + m.degree p₁ x = t₁ x := by
        exact congrFun (congrArg DFunLike.coe hs₁) x
      have h₂x : m.degree p₂ x ≤ t₁ x := hle₂t x
      change
        ((t₁ - (m.degree p₁ ⊔ m.degree p₂)) x) +
            (((m.degree p₁ ⊔ m.degree p₂) - m.degree p₁) x) =
          s₁ x
      rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
      change
        t₁ x - max (m.degree p₁ x) (m.degree p₂ x) +
            (max (m.degree p₁ x) (m.degree p₂ x) - m.degree p₁ x) =
          s₁ x
      omega
    have hv₂ : v + (l - m.degree p₂) = s₂ := by
      unfold v l
      ext x
      have hsx : s₂ x + m.degree p₂ x = t₁ x := by
        exact congrFun (congrArg DFunLike.coe hs₂t) x
      have h₁x : m.degree p₁ x ≤ t₁ x := hle₁t x
      change
        ((t₁ - (m.degree p₁ ⊔ m.degree p₂)) x) +
            (((m.degree p₁ ⊔ m.degree p₂) - m.degree p₂) x) =
          s₂ x
      rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
      change
        t₁ x - max (m.degree p₁ x) (m.degree p₂ x) +
            (max (m.degree p₁ x) (m.degree p₂ x) - m.degree p₂ x) =
          s₂ x
      omega
    have hk₂ : k * m.leadingCoeff p₂ = c₁ := by
      unfold k
      rw [← hu₂]
      simp [mul_assoc]
    have hcoeff_eq :
        c₁ * m.leadingCoeff p₁ = c₂ * m.leadingCoeff p₂ := by
      rw [hc₁, hc₂t]
    have hk₁ : k * m.leadingCoeff p₁ = c₂ := by
      calc
        k * m.leadingCoeff p₁
            = (c₁ * ↑u₂⁻¹) * m.leadingCoeff p₁ := rfl
        _ = (c₁ * m.leadingCoeff p₁) * ↑u₂⁻¹ := by ring
        _ = (c₂ * m.leadingCoeff p₂) * ↑u₂⁻¹ := by rw [hcoeff_eq]
        _ = c₂ := by
          rw [← hu₂]
          simp [mul_assoc]
    have hq_spol :
        q₁ - q₂ = monomial v k * m.sPolynomial p₁ p₂ := by
      calc
        q₁ - q₂
            =
              monomial v k *
                (monomial (l - m.degree p₁) (m.leadingCoeff p₂) * p₁ -
                  monomial (l - m.degree p₂) (m.leadingCoeff p₁) * p₂) := by
                unfold q₁ q₂
                rw [mul_sub]
                simp only [← mul_assoc]
                rw [monomial_mul, monomial_mul, hv₁, hv₂, hk₂, hk₁]
        _ = monomial v k * m.sPolynomial p₁ p₂ := by
              rw [sPolynomial_def]
    have hmul :
        monomial v k * m.sPolynomial p₁ p₂ ⟶*[m, G]
          monomial v k * 0 :=
      monomial_mul_reflTransGen m v k G (hspol p₁ hp₁G p₂ hp₂G)
    simpa [hq_spol] using hmul
  · have ht_ne_syn : m.toSyn t₁ ≠ m.toSyn t₂ := by
      intro hsyn
      exact ht (m.toSyn.injective hsyn)
    rcases lt_or_gt_of_ne ht_ne_syn with ht₁_lt_t₂ | ht₂_lt_t₁
    · have hq₁_coeff_t₂ : q₁.coeff t₂ = 0 := by
        apply m.coeff_eq_zero_of_lt
        simpa [hq₁_degree] using ht₁_lt_t₂
      have hstep₁ : q₁ - q₂ ⟶[m, G] q₁ := by
        refine ⟨p₂, hp₂G, t₂, hp₂, ?_, s₂, hs₂, -c₂, ?_, ?_⟩
        · rw [MvPolynomial.mem_support_iff, coeff_sub, hq₁_coeff_t₂, hq₂_coeff]
          simpa [sub_eq_add_neg, neg_mul] using
            (neg_ne_zero.mpr hc₂_ne_prod)
        · rw [coeff_sub, hq₁_coeff_t₂, hq₂_coeff]
          ring
        · unfold q₂
          have hmon_neg :
              monomial s₂ (-c₂) = -(monomial s₂ c₂ : MvPolynomial σ R) := by
            ext d
            by_cases hds : d = s₂ <;> simp [coeff_monomial, hds]
          rw [hmon_neg]
          ring
      have hstep₂ : q₁ ⟶[m, G] 0 :=
        monomial_mul_mem_reducesTo_zero m G hp₁G hp₁ s₁ hc₁_ne_prod
      exact (Relation.ReflTransGen.single hstep₁).trans
        (Relation.ReflTransGen.single hstep₂)
    · have hq₂_coeff_t₁ : q₂.coeff t₁ = 0 := by
        apply m.coeff_eq_zero_of_lt
        simpa [hq₂_degree] using ht₂_lt_t₁
      have hstep₁ : q₁ - q₂ ⟶[m, G] -q₂ := by
        refine ⟨p₁, hp₁G, t₁, hp₁, ?_, s₁, hs₁, c₁, ?_, ?_⟩
        · rw [MvPolynomial.mem_support_iff, coeff_sub, hq₁_coeff, hq₂_coeff_t₁,
            sub_zero]
          exact hc₁_ne_prod
        · rw [coeff_sub, hq₁_coeff, hq₂_coeff_t₁, sub_zero]
        · unfold q₁
          ring
      have hstep₂ : -q₂ ⟶[m, G] 0 := by
        have hneg :
            (-c₂) * m.leadingCoeff p₂ ≠ 0 := by
          simpa [neg_mul] using neg_ne_zero.mpr hc₂_ne_prod
        have hred :
            monomial s₂ (-c₂) * p₂ ⟶[m, G] 0 :=
          monomial_mul_mem_reducesTo_zero m G hp₂G hp₂ s₂ hneg
        simpa [q₂] using hred
      exact (Relation.ReflTransGen.single hstep₁).trans
        (Relation.ReflTransGen.single hstep₂)

/--
Theorem 5.48, equivalence of items `(i)` and `(iii)`.

A set `G` is a Gröbner basis iff every S-polynomial of two elements of `G`
reduces to zero modulo `G`.
-/
theorem iff_sPolynomial_reflTransGen_zero
    [NoZeroDivisors R]
    (G : Set (MvPolynomial σ R))
    (hG₀ : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0) :
    m.IsGroebner G ↔
      ∀ g₁ ∈ G, ∀ g₂ ∈ G,
        m.sPolynomial g₁ g₂ ⟶*[m, G] 0 := by
  constructor
  · intro hG g₁ hg₁ g₂ hg₂
    exact sPolynomial_reflTransGen_zero m G hG₀ hG hg₁ hg₂
  · exact of_sPolynomial_reflTransGen_zero m G hG₀

end CommRing

end IsGroebner

namespace IsGroebnerBasis

section CommRing

variable {R : Type*} [CommRing R]

/--
Theorem 5.48, forward implication for the ideal-relative definition.

If `G` is a Gröbner basis of `I`, then every S-polynomial of two elements of
`G` reduces to zero modulo `G`.
-/
theorem sPolynomial_reflTransGen_zero
    (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R))
    (hG₀ : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (hGB : m.IsGroebnerBasis G I)
    {g₁ g₂ : MvPolynomial σ R}
    (hg₁ : g₁ ∈ G)
    (hg₂ : g₂ ∈ G) :
    m.sPolynomial g₁ g₂ ⟶*[m, G] 0 := by
  exact IsGroebner.sPolynomial_reflTransGen_zero m G hG₀
    (IsGroebnerBasis.isGroebner (m := m) hGB) hg₁ hg₂

/--
Theorem 5.48, normal-form forward implication for the ideal-relative
definition.

If `G` is a Gröbner basis of `I`, then every normal form of an S-polynomial
of two elements of `G` is zero.
-/
theorem normalForm_sPolynomial_eq_zero
    (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R))
    (hG₀ : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (hGB : m.IsGroebnerBasis G I)
    {g₁ g₂ h : MvPolynomial σ R}
    (hg₁ : g₁ ∈ G)
    (hg₂ : g₂ ∈ G)
    (hnf : Relation.IsNormalFormOf
      (m.ReducesToSet G) (m.sPolynomial g₁ g₂) h) :
    h = 0 := by
  exact IsGroebner.normalForm_sPolynomial_eq_zero m G hG₀
    (IsGroebnerBasis.isGroebner (m := m) hGB) hg₁ hg₂ hnf

/--
Theorem 5.48, reverse implication for the ideal-relative definition.

If `G` generates `I` and every S-polynomial of two elements of `G` reduces to
zero modulo `G`, then `G` is a Gröbner basis of `I`.
-/
theorem of_sPolynomial_reflTransGen_zero
    [NoZeroDivisors R]
    (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R))
    (hspan : Ideal.span G = I)
    (hG₀ : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0)
    (hspol :
      ∀ g₁ ∈ G, ∀ g₂ ∈ G,
        m.sPolynomial g₁ g₂ ⟶*[m, G] 0) :
    m.IsGroebnerBasis G I := by
  constructor
  · intro g hg
    rw [← hspan]
    exact Ideal.subset_span hg
  · rw [← hspan]
    exact IsGroebner.of_sPolynomial_reflTransGen_zero m G hG₀ hspol

/--
Theorem 5.48, equivalence of items `(i)` and `(iii)` for an explicitly
specified ideal `I` generated by `G`.
-/
theorem iff_sPolynomial_reflTransGen_zero
    [NoZeroDivisors R]
    (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R))
    (hspan : Ideal.span G = I)
    (hG₀ : ∀ g ∈ G, IsUnit (m.leadingCoeff g) ∨ g = 0) :
    m.IsGroebnerBasis G I ↔
      ∀ g₁ ∈ G, ∀ g₂ ∈ G,
        m.sPolynomial g₁ g₂ ⟶*[m, G] 0 := by
  constructor
  · intro hGB g₁ hg₁ g₂ hg₂
    exact sPolynomial_reflTransGen_zero m G I hG₀ hGB hg₁ hg₂
  · exact of_sPolynomial_reflTransGen_zero m G I hspan hG₀

end CommRing

end IsGroebnerBasis

end MonomialOrder
