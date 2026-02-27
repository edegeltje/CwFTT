import CwFTT.Classifier.Colimit
import CwFTT.Classifier.Ops.And

namespace CategoryTheory
open Limits
universe v u
variable {C : Type u} [Category.{v} C]


/--
an equivalent definition can be defined when we have "forall", via the statement
`∀ p : Prop, p`, which might be computable, although it probably requires chosen pullbacks.
-/
noncomputable def Classifier.falsity (𝒞 : Classifier C) [HasInitial C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] : 𝒞.Ω₀ ⟶ 𝒞.Ω :=
  𝒞.χ ((initial.to 𝒞.Ω₀))

lemma Classifier.falsity_isPullback (𝒞 : Classifier C) [HasInitial C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] :
    IsPullback (initial.to 𝒞.Ω₀) (𝒞.χ₀ _) 𝒞.falsity 𝒞.truth := by
  exact 𝒞.isPullback (initial.to 𝒞.Ω₀)

open MonoidalCategory CartesianMonoidalCategory

private lemma Classifier.falsity_and_aux (𝒞 : Classifier C) [HasInitial C]
    [CartesianMonoidalCategory C] [MonoidalClosed C]
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    lift (𝒞.χ f) (𝒞.χ₀ _ ≫ 𝒞.falsity) ≫ 𝒞.and = 𝒞.χ₀ _ ≫ 𝒞.falsity := by
  apply 𝒞.hom_ext _ _ (m := initial.to _)
    ((𝟙 (⊥_ C) ≫ lift (initial.to X) (initial.to (⊥_ C)) ≫ (𝒞.χ₀ _ ⊗ₘ 𝒞.χ₀ _)) ≫
      𝒞.χ₀ (𝒞.Ω₀ ⊗ 𝒞.Ω₀))
    (𝟙 _ ≫ 𝒞.χ₀ _)
  · apply IsPullback.paste_vert _ (𝒞.and_isPullback)
    · rw [← Category.id_comp (𝒞.χ f),← lift_map]
      apply IsPullback.paste_vert (.initial_to_hori _)
      apply IsPullback.of_iso (IsPullback.tensor (𝒞.isPullback f) (
        IsPullback.paste_vert (IsPullback.initial_to_hori (𝒞.χ₀ _)) 𝒞.falsity_isPullback))
        (asIso (snd _ _)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by
          simp only [Iso.refl_hom, Category.comp_id]
          rw [← Iso.inv_comp_eq, Subsingleton.elim (asIso _).inv (initial.to _)]
          apply CartesianMonoidalCategory.hom_ext <;> simp)
        (by
          apply CartesianMonoidalCategory.hom_ext <;> simp)
        (by simp) (by simp)
  · apply IsPullback.paste_vert (IsPullback.initial_to_hori _) (𝒞.falsity_isPullback)

lemma Classifier.falsity_and (𝒞 : Classifier C) [HasInitial C]
    [CartesianMonoidalCategory C] [MonoidalClosed C]
    {X : C} (f : X ⟶ 𝒞.Ω) : lift (𝒞.χ₀ _ ≫ 𝒞.falsity) f ≫ 𝒞.and = 𝒞.χ₀ _ ≫ 𝒞.falsity := by
  rw [← Category.comp_id f, ← 𝒞.χ_truth, ← 𝒞.comp_χ₀_assoc f, ← comp_lift_assoc,
    and_comm, 𝒞.falsity_and_aux]

noncomputable instance [HasInitial C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    (𝒞 : Classifier C) (X : C) :
    OrderBot (X ⟶ 𝒞.Ω) where
  bot := 𝒞.χ₀ _ ≫ 𝒞.falsity
  bot_le f := by
    rw [𝒞.le_def, 𝒞.falsity_and]

lemma Classifier.and_falsity (𝒞 : Classifier C) [HasInitial C]
    [CartesianMonoidalCategory C] [MonoidalClosed C]
    {X : C} (f : X ⟶ 𝒞.Ω) :
    lift f (𝒞.χ₀ _ ≫ 𝒞.falsity) ≫ 𝒞.and = 𝒞.χ₀ _ ≫ 𝒞.falsity := by
  rw [and_comm, 𝒞.falsity_and]

lemma χ_to_eq_falsity (𝒞 : Classifier C) {I : C} (hI : IsInitial I)
    [CartesianMonoidalCategory C] [MonoidalClosed C] :
    letI : HasInitial C := IsInitial.hasInitial hI
    letI := initial_mono _ hI
    @𝒞.χ _ _ _ (hI.to 𝒞.Ω₀) this = 𝒞.falsity := by
  have : HasInitial C := IsInitial.hasInitial hI
  have := initial_mono 𝒞.Ω₀ hI
  refine 𝒞.hom_ext _ _ (𝒞.χ₀ _) _ ?_ (𝒞.isPullback (initial.to 𝒞.Ω₀))
  rw [← initial.to_comp (hI.to 𝒞.Ω₀),← Category.id_comp 𝒞.truth]
  have := strict_initial hI (initial.to I)
  exact IsPullback.paste_horiz (.of_horiz_isIso_mono (by simp)) (𝒞.isPullback _)

lemma eq_true_of_falsity_eq_true (𝒞 : Classifier C) [HasInitial C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] (h : 𝒞.falsity = 𝒞.truth)
    {X Y : C} (f : X ⟶ Y) [Mono f] : 𝒞.χ f = 𝒞.χ₀ _ ≫ 𝒞.truth := by
  nth_rw 1 [← 𝒞.and_truth (𝒞.χ f), ← h, 𝒞.and_falsity,h]

end CategoryTheory
