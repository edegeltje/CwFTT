import CwFTT.Classifier.Basic


namespace CategoryTheory
open Limits
universe v u
variable {C : Type u} [Category.{v} C]

section and
open MonoidalCategory CartesianMonoidalCategory

instance [CartesianMonoidalCategory C] {A B D E : C} (f : A ⟶ B) [Mono f] (g : D ⟶ E) [Mono g] :
    Mono (f ⊗ₘ g) := by
  rw [tensorHom_def]
  infer_instance

abbrev Classifier.and [CartesianMonoidalCategory C] (𝒞 : Classifier C) :
    𝒞.Ω ⊗ 𝒞.Ω ⟶ 𝒞.Ω :=
  𝒞.χ (𝒞.truth ⊗ₘ 𝒞.truth)

lemma Classifier.and_isPullback (𝒞 : Classifier C) [CartesianMonoidalCategory C] :
    IsPullback (𝒞.truth ⊗ₘ 𝒞.truth) (𝒞.χ₀ _) (𝒞.and) (𝒞.truth) := 𝒞.isPullback _

lemma Classifier.and_eq_truth_iff (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    {X : C} (f g : X ⟶ 𝒞.Ω) :
    lift f g ≫ 𝒞.and = 𝒞.χ₀ _ ≫ 𝒞.truth ↔ (f = 𝒞.χ₀ _ ≫ 𝒞.truth ∧ g = 𝒞.χ₀ _ ≫ 𝒞.truth) := by
  constructor
  · intro h
    suffices lift f g = 𝒞.χ₀ _ ≫ lift 𝒞.truth 𝒞.truth by
      simpa using And.intro (congr($this ≫ fst _ _)) (congr($this ≫ snd _ _))
    rw [← 𝒞.and_isPullback.lift_fst _ _ h]
    nth_rw 6 7 [← Category.id_comp 𝒞.truth]
    rw [← lift_map, ← Category.assoc]
    congr 1
    ext <;> simpa using Subsingleton.elim _ _
  · rintro ⟨rfl,rfl⟩
    rw [← lift_map_assoc, 𝒞.and_isPullback.w, 𝒞.comp_χ₀_assoc]

lemma Classifier.χ_pullback [CartesianMonoidalCategory C] {𝒞 : Classifier C} {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} [Mono f₃] {f₄ : X₃ ⟶ X₄} [Mono f₄]
    (hf : IsPullback f₁ f₂ f₃ f₄) :
    letI : Mono (f₁ ≫ f₃) := mono_comp' (hf.mono_fst) inferInstance
    𝒞.χ (f₁ ≫ f₃) = lift (𝒞.χ f₃) (𝒞.χ f₄) ≫ 𝒞.and := by
  symm
  have : Mono (f₁ ≫ f₃) := mono_comp' (hf.mono_fst) inferInstance
  refine 𝒞.uniq _ (χ₀' := 𝒞.χ₀ _) ?_
  rw [Classifier.truth]
  convert IsPullback.paste_vert
    (IsPullback.pullback_fst_monoidal (𝒞.isPullback f₃) (𝒞.isPullback f₄) hf)
    (𝒞.isPullback (𝒞.truth ⊗ₘ 𝒞.truth))
  apply Subsingleton.elim

-- #synth CartesianMonoidalCategory (C ⥤ Type (max u v))

attribute [local instance] CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory in
lemma Classifier.and_comm_aux [CartesianMonoidalCategory C] (𝒞 : Classifier C) :
    (β_ _ _).hom ≫ 𝒞.and = 𝒞.and := by
  dsimp [Classifier.and]
  apply 𝒞.uniq _ (χ₀' := (β_ _ _).hom ≫ 𝒞.χ₀ _)
  have : IsPullback (𝒞.truth ⊗ₘ 𝒞.truth)
      (β_ _ _).hom (β_ _ _).hom (𝒞.truth ⊗ₘ 𝒞.truth) := by
    exact .of_vert_isIso_mono (by simp)
  exact (this).paste_vert (𝒞.isPullback (𝒞.truth ⊗ₘ 𝒞.truth))

lemma Classifier.and_comm [CartesianMonoidalCategory C] (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) :
    CartesianMonoidalCategory.lift f g ≫ 𝒞.and = CartesianMonoidalCategory.lift g f ≫ 𝒞.and := by
  nth_rw 1 [← 𝒞.and_comm_aux]
  simp

lemma Classifier.and_assoc_aux [CartesianMonoidalCategory C] (𝒞 : Classifier C) :
    (α_ _ _ _).hom ≫ (𝒞.Ω ◁ 𝒞.and) ≫ 𝒞.and = (𝒞.and ▷ 𝒞.Ω) ≫ 𝒞.and := by
  rw [← tensorHom_id, ← id_tensorHom]
  apply 𝒞.hom_ext _ _ (m := ((𝒞.truth) ⊗ₘ 𝒞.truth) ⊗ₘ (𝒞.truth))
  · have assoc : IsPullback ((𝒞.truth ⊗ₘ 𝒞.truth) ⊗ₘ 𝒞.truth)
        (α_ _ _ _).hom (α_ _ _ _).hom
        (𝒞.truth ⊗ₘ (𝒞.truth ⊗ₘ 𝒞.truth)) := by
      exact .of_vert_isIso_mono (by simp)
    have := ((IsPullback.id_vert 𝒞.truth).tensor 𝒞.and_isPullback).paste_vert 𝒞.and_isPullback
    exact assoc.paste_vert this
  · exact (𝒞.and_isPullback.tensor (IsPullback.id_vert 𝒞.truth)).paste_vert 𝒞.and_isPullback

lemma Classifier.and_assoc [CartesianMonoidalCategory C] (𝒞 : Classifier C) {X : C}
    (f g h : X ⟶ 𝒞.Ω) :
    CartesianMonoidalCategory.lift (CartesianMonoidalCategory.lift f g ≫ 𝒞.and) h ≫ 𝒞.and =
    CartesianMonoidalCategory.lift f (CartesianMonoidalCategory.lift g h ≫ 𝒞.and) ≫ 𝒞.and := by
  trans CartesianMonoidalCategory.lift (CartesianMonoidalCategory.lift f g) h ≫
    (𝒞.and ▷ 𝒞.Ω) ≫ 𝒞.and
  · simp
  · simp [← 𝒞.and_assoc_aux]

lemma Classifier.isPullback_of_isPullback_and [CartesianMonoidalCategory C] (𝒞 : Classifier C)
    {X Y Z : C} (f : X ⟶ Z) [Mono f] (g : Y ⟶ Z) [Mono g] {W : C} {fst : W ⟶ X} {snd : W ⟶ Y}
    (h : fst ≫ f = snd ≫ g) (hpb : IsPullback (fst ≫ f) (𝒞.χ₀ _)
      (CartesianMonoidalCategory.lift (𝒞.χ f) (𝒞.χ g) ≫ 𝒞.and) (𝒞.truth)) :
    IsPullback fst snd f g := by
  apply IsPullback.of_pullback_monoidal _
  apply IsPullback.of_bot _ (by simp [h]) ((𝒞.isPullback f).tensor (𝒞.isPullback g))
  simp only [CartesianMonoidalCategory.lift_map, comp_χ₀, Category.id_comp]
  apply IsPullback.of_bot _ (by
    apply CartesianMonoidalCategory.hom_ext
    · simp [(𝒞.isPullback f).w]
    · simp [reassoc_of% h, (𝒞.isPullback g).w]) (𝒞.and_isPullback)
  simpa

open CartesianMonoidalCategory

@[reassoc (attr := simp)]
lemma Classifier.and_truth [CartesianMonoidalCategory C] (𝒞 : Classifier C)
    {X : C} (f : X ⟶ 𝒞.Ω) : lift f (𝒞.χ₀ _ ≫ 𝒞.truth) ≫ 𝒞.and = f := by
  rw [← Category.comp_id f, ← 𝒞.comp_χ₀_assoc f,
    ← comp_lift_assoc,← 𝒞.χ_truth,← 𝒞.χ_id, ← 𝒞.χ_pullback (.id_horiz _)]
  simp

@[reassoc (attr := simp)]
lemma Classifier.truth_and [CartesianMonoidalCategory C] (𝒞 : Classifier C)
    {X : C} (f : X ⟶ 𝒞.Ω) [HasPullback f 𝒞.truth] : lift (𝒞.χ₀ _ ≫ 𝒞.truth) f ≫ 𝒞.and = f := by
  rw [𝒞.and_comm, 𝒞.and_truth]

lemma Classifier.χ_and_eq_self_iff [CartesianMonoidalCategory C] (𝒞 : Classifier C)
    {X Z : C} (f : X ⟶ Z) [Mono f] (g : Z ⟶ 𝒞.Ω) :
    lift (𝒞.χ f) g ≫ 𝒞.and = 𝒞.χ f ↔ f ≫ g = 𝒞.χ (𝟙 _) := by
  constructor
  · intro h
    rw [← 𝒞.and_truth (g), comp_lift_assoc,𝒞.comp_χ₀_assoc,
      ← (𝒞.isPullback f).w,← comp_lift_assoc,𝒞.and_comm,h, (𝒞.isPullback f).w,
      𝒞.χ_id]
  · intro h
    apply 𝒞.uniq
    apply IsPullback.paste_vert (v₁₁ := lift (𝒞.χ₀ _) (𝒞.χ₀ _)) _ 𝒞.and_isPullback
    -- i hope there's a more elegant way to prove this...
    -- the key seems to be with showing that the square commutes
    refine {
      w := by simp [(𝒞.isPullback f).w, h, (𝒞.χ_id X)]
      isLimit' := by
        constructor
        refine PullbackCone.IsLimit.mk _
          (fun s => (𝒞.isPullback f).lift
            s.fst (s.snd ≫ fst _ _) (by simpa using congr($(s.condition) ≫ fst _ _)))
          (by simp only [IsPullback.lift_fst, implies_true])
          (by
            intro s
            simp only [comp_lift, comp_χ₀]
            apply CartesianMonoidalCategory.hom_ext <;> apply Subsingleton.elim)
          (by
            intro s m hm₁ hm₂
            apply Mono.right_cancellation (f := f)
            simp [hm₁])
    }

/-
REMINDER: EVERY MORPHISM `X ⟶ 𝒞.Ω` FACTORS THROUGH SOME `χ`, namely `𝒞.χ 𝒞.truth`
-/

/-- and is reflexive -/
lemma Classifier.and_refl [CartesianMonoidalCategory C] (𝒞 : Classifier C)
    {X : C} (f : X ⟶ 𝒞.Ω) : lift f f ≫ 𝒞.and = f := by
  rw [← Category.comp_id f, ← comp_lift_assoc, ← 𝒞.χ_truth]
  congr 1
  apply 𝒞.uniq
  · rw [← Category.comp_id (𝒞.χ 𝒞.truth), ← comp_lift_assoc]
    apply IsPullback.paste_vert (𝒞.isPullback (𝒞.truth))
    · convert IsPullback.paste_vert (.pullback_monoidal (IsKernelPair.id_of_mono 𝒞.truth))
        (𝒞.and_isPullback)
      simp

end and

section le
variable [CartesianMonoidalCategory C]

instance (𝒞 : Classifier C) (X : C) : LE (X ⟶ 𝒞.Ω) where
  le f g := CartesianMonoidalCategory.lift f g ≫ 𝒞.and = f

lemma Classifier.le_def (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) :
  f ≤ g ↔ (CartesianMonoidalCategory.lift f g ≫ 𝒞.and = f) := Iff.rfl

alias Classifier.le_iff_and_eq_left := Classifier.le_def

instance (𝒞 : Classifier C) (X : C) :
    SemilatticeInf (X ⟶ 𝒞.Ω) where
  le_refl a := by -- 𝒞.and is co-diagonal(?)
    rw [𝒞.le_def, 𝒞.and_refl]
  le_trans a b c hab hbc := by -- 𝒞.and is associative
    rw [Classifier.le_def] at hab hbc ⊢
    nth_rw 1 2 [← hab,𝒞.and_assoc,hbc]
  le_antisymm a b hab hba := by -- 𝒞.and is commutative
    rw [← hab,𝒞.and_comm,hba]
  inf f g := (CartesianMonoidalCategory.lift f g) ≫ 𝒞.and
  inf_le_left f g := by
    rw [𝒞.le_def, 𝒞.and_comm f g, 𝒞.and_assoc, 𝒞.and_refl f]
  inf_le_right f g := by
    rw [𝒞.le_def, 𝒞.and_assoc, 𝒞.and_refl g]
  le_inf a b c hab hac := by
    rw [𝒞.le_def,← 𝒞.and_assoc,hab,hac]

lemma Classifier.inf_def (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) :
  f ⊓ g = CartesianMonoidalCategory.lift f g ≫ 𝒞.and := rfl

lemma Classifier.comp_inf (𝒞 : Classifier C) {X Y : C} (j : X ⟶ Y) (f g : Y ⟶ 𝒞.Ω) :
    j ≫ (f ⊓ g) = (j ≫ f) ⊓ (j ≫ g) := by
  simp [inf_def,CartesianMonoidalCategory.comp_lift_assoc]

instance (𝒞 : Classifier C) (X : C) : OrderTop (X ⟶ 𝒞.Ω) where
  top := 𝒞.χ₀ X ≫ 𝒞.truth
  le_top := by
    intro f
    rw [𝒞.le_def, 𝒞.and_truth]

lemma Classifier.top_def (𝒞 : Classifier C) (X : C) : (⊤ : X ⟶ 𝒞.Ω) = 𝒞.χ₀ _ ≫ 𝒞.truth := rfl

lemma Classifier.comp_top (𝒞 : Classifier C) {X Y : C} (j : X ⟶ Y) : j ≫ (⊤ : Y ⟶ 𝒞.Ω) = ⊤ := by
  rw [𝒞.top_def,𝒞.comp_χ₀_assoc,𝒞.top_def]

lemma Classifier.precomp_monotone (𝒞 : Classifier C) {X Y : C} (f : X ⟶ Y) :
    Monotone (f ≫ · : (Y ⟶ 𝒞.Ω) → (X ⟶ 𝒞.Ω)) := by
  intro g h hle
  rw [𝒞.le_def, ← CartesianMonoidalCategory.comp_lift_assoc, hle]

lemma Classifier.precomp_antitone (𝒞 : Classifier C) {X Y : C} (f : X ⟶ Y) [Epi f] :
    Antitone (f ≫ · : (Y ⟶ 𝒞.Ω) → (X ⟶ 𝒞.Ω)) := by
  intro g h hle
  dsimp only
  rw [𝒞.le_def, ← CartesianMonoidalCategory.comp_lift_assoc]
  rw [cancel_epi, ← 𝒞.le_def]

  sorry

-- lemma Classifier.precomp_reflect_le (𝒞 : Classifier C) {X Y : C} (f : X ⟶ Y) [Epi f]
--     StrictMono ()

end le


end CategoryTheory
