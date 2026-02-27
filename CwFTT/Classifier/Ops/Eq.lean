import CwFTT.Classifier.Basic

namespace CategoryTheory
open Limits
universe v u
variable {C : Type u} [Category.{v} C]

open MonoidalCategory CartesianMonoidalCategory

def Classifier.eq (𝒞 : Classifier C) [CartesianMonoidalCategory C] (X : C) :
    X ⊗ X ⟶ 𝒞.Ω :=
  𝒞.χ (lift (𝟙 X) (𝟙 X))

lemma Classifier.eq_isPullback (𝒞 : Classifier C) [CartesianMonoidalCategory C] (X : C) :
    IsPullback (lift (𝟙 X) (𝟙 X)) (𝒞.χ₀ _) (𝒞.eq X) 𝒞.truth := 𝒞.isPullback _

/-- `𝒞.eq` internalizes equality -/
lemma Classifier.eq_eq_truth_iff (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    {X Y : C} (f g : X ⟶ Y) :
    lift f g ≫ 𝒞.eq Y = 𝒞.χ₀ _ ≫ 𝒞.truth ↔ f = g := by
  constructor
  · intro h
    nth_rw 1 [← lift_snd f g,← lift_fst f g]
    rw [← (𝒞.eq_isPullback Y).lift_fst _ _ h, Category.assoc,Category.assoc,
      lift_fst,lift_snd]
  · rintro rfl
    rw [← Category.comp_id f, ← comp_lift_assoc, (𝒞.eq_isPullback Y).w,
      𝒞.comp_χ₀_assoc]

attribute [local instance] CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory in
lemma Classifier.eq_comm_aux (𝒞 : Classifier C) [CartesianMonoidalCategory C] (X : C) :
    (β_ X X).hom ≫ 𝒞.eq X = 𝒞.eq X := by
  apply 𝒞.hom_ext _ _ (𝟙 _ ≫ 𝒞.χ₀ _) _ _ (𝒞.eq_isPullback _)
  apply IsPullback.paste_vert (.of_vert_isIso_mono _) (𝒞.eq_isPullback _)
  simp

lemma Classifier.eq_comm (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    {X Y : C} (f g : X ⟶ Y) :
    lift f g ≫ 𝒞.eq Y = lift g f ≫ 𝒞.eq Y := by
  let : BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
  nth_rw 1 [← 𝒞.eq_comm_aux, lift_braiding_hom_assoc]


lemma Classifier.eq_refl (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    {X Y : C} (f : X ⟶ Y) : (lift f f ≫ 𝒞.eq Y) = 𝒞.χ₀ _ ≫ 𝒞.truth := by
  rw [← Category.comp_id f, ← comp_lift_assoc,(𝒞.eq_isPullback _).w,𝒞.comp_χ₀_assoc]

-- concludable from eq_eq_iff
lemma Classifier.eq_true_eq (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    {X : C} (f : X ⟶ 𝒞.Ω) : (lift f (𝒞.χ₀ _ ≫ 𝒞.truth) ≫ 𝒞.eq _) = f := by
  rw [← Category.comp_id f, ← 𝒞.comp_χ₀_assoc f, ← comp_lift_assoc]
  congr 1
  clear f X -- wlog, `X = 𝒞.Ω` and `f = 𝟙 𝒞.Ω`
  apply Eq.trans _ 𝒞.χ_truth
  apply 𝒞.uniq _ (χ₀' := (𝒞.truth ≫ 𝒞.χ₀ _))
  apply IsPullback.of_iso _ (Iso.refl _) (Iso.mk (fst _ _) (lift (𝟙 _) (𝒞.χ₀ _))) (Iso.refl _)
    (Iso.refl _) (by rw [← Iso.eq_comp_inv]) (by simp;rfl) (by simp;rfl) (by simp;rfl)
  simp only [Iso.refl_hom, Category.id_comp, comp_lift, Category.comp_id, comp_χ₀, χ₀_Ω₀]
  have := (IsPullback.pullback_monoidal (.id_vert 𝒞.truth)).flip
  have := this.paste_vert (𝒞.eq_isPullback _)
  simp only [Category.comp_id, comp_χ₀, χ₀_Ω₀, id_tensorHom] at this
  convert this using 1
  · rw [← Category.assoc]
    congr 1
    ext <;> simp [Subsingleton.elim (𝒞.χ₀ _) (snd 𝒞.Ω _)]


end CategoryTheory
