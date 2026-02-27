import CwFTT.Util.Cartesian
import CwFTT.Util.Pullback

universe v u
namespace CategoryTheory
variable {C : Type u} [Category.{v} C]
open Limits MonoidalCategory CartesianMonoidalCategory

open MonoidalCategory

lemma _root_.CategoryTheory.IsPullback.tensor [CartesianMonoidalCategory C]
    {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₁ ⟶ Y₃} {g₃ : Y₂ ⟶ Y₄} {g₄ : Y₃ ⟶ Y₄} (hg : IsPullback g₁ g₂ g₃ g₄) :
    IsPullback (f₁ ⊗ₘ g₁) (f₂ ⊗ₘ g₂) (f₃ ⊗ₘ g₃) (f₄ ⊗ₘ g₄) := by
  refine ⟨⟨?_⟩,⟨?_⟩⟩
  · simp [hf.w,hg.w]
  · refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro s
      have := s.condition
      simp only [CartesianMonoidalCategory.hom_ext_iff, Category.assoc, tensorHom_fst,
        tensorHom_snd] at this
      apply lift
      · fapply hf.lift (s.fst ≫ fst _ _) (s.snd ≫ fst _ _)
        simpa using this.left
      · fapply hg.lift (s.fst ≫ snd _ _) (s.snd ≫ snd _ _)
        simpa using this.right
    · intro s
      simp
    · intro s
      simp
    · intro s m hm₁ hm₂
      simp_all only [CartesianMonoidalCategory.hom_ext_iff, Category.assoc, tensorHom_fst,
        tensorHom_snd, lift_fst, lift_snd]
      constructor
      · apply hf.hom_ext
        · simpa using hm₁.left
        · simpa using hm₂.left
      · apply hg.hom_ext
        · simpa using hm₁.right
        · simpa using hm₂.right

lemma IsPullback.whiskerRight_horiz [CartesianMonoidalCategory C] {X Y : C} (f : X ⟶ Y) (Z : C) :
    IsPullback (f ▷ Z) (fst X Z) (fst Y Z) f := by
  refine IsPullback.of_isLimit' (by simp) ?_
  apply PullbackCone.IsLimit.mk _ (
    fun s => CartesianMonoidalCategory.lift s.snd (s.fst ≫ snd _ _)
  )
  · intro s
    ext <;> simp [s.condition]
  · intro s
    simp
  · intro s m hm₁ hm₂
    ext
    · simpa
    · simp [← hm₁]

lemma IsPullback.braiding_vert [MonoidalCategory C] [BraidedCategory C] {X₁ X₂ X₃ X₄ : C}
    (f : X₁ ⟶ X₃) (g : X₂ ⟶ X₄) :
    IsPullback (f ⊗ₘ g) (β_ X₁ X₂).hom (β_ _ _).hom (g ⊗ₘ f) :=
  .of_vert_isIso (by simp)

lemma IsPullback.whiskerLeft_horiz [CartesianMonoidalCategory C] {X Y : C} (f : X ⟶ Y) (Z : C) :
    IsPullback (Z ◁ f) (snd Z X) (snd Z Y) f := by
  have := BraidedCategory.ofCartesianMonoidalCategory (C := C)
  have hleft := IsPullback.whiskerRight_horiz f Z
  have := (IsPullback.braiding_vert (𝟙 Z) f)
  simp only [tensorHom_id, id_tensorHom] at this
  convert this.paste_vert hleft <;> simp

variable [CartesianMonoidalCategory C]

lemma IsPullback.pullback_monoidal {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃}
    {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄) :
    IsPullback (f₁ ≫ f₃)
      (CartesianMonoidalCategory.lift f₁ f₂) (CartesianMonoidalCategory.lift (𝟙 X₄) (𝟙 _))
      (f₃ ⊗ₘ f₄) where
  w := by
    apply CartesianMonoidalCategory.hom_ext_iff.mpr
    simp [hf.w]
  isLimit' := by
    constructor
    refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro s
      refine hf.lift (s.snd ≫ fst _ _) (s.snd ≫ snd _ _) ?_
      have := s.condition
      simp only [CartesianMonoidalCategory.comp_lift, Category.comp_id,
        CartesianMonoidalCategory.hom_ext_iff, CartesianMonoidalCategory.lift_fst, Category.assoc,
        tensorHom_fst, CartesianMonoidalCategory.lift_snd, tensorHom_snd] at this
      simp [this.left, ← this.right]
    · intro s
      simp only [IsPullback.lift_fst_assoc, Category.assoc]
      have := s.condition
      simp [CartesianMonoidalCategory.hom_ext_iff] at this
      exact this.left.symm
    · cat_disch
    · intro s m hm₁ hm₂
      simp only [CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.hom_ext_iff,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd] at hm₂ ⊢
      apply hf.hom_ext
      -- apply Limits.prod.hom_ext
      · simpa using hm₂.left
      · simpa [hm₁] using hm₂.right

lemma IsPullback.of_pullback_monoidal {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃}
    {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hpb : IsPullback (f₁ ≫ f₃)
      (CartesianMonoidalCategory.lift f₁ f₂) (CartesianMonoidalCategory.lift (𝟙 X₄) (𝟙 _))
      (f₃ ⊗ₘ f₄)) : IsPullback f₁ f₂ f₃ f₄ where
  w := by simpa using congr($(hpb.w) ≫ CartesianMonoidalCategory.snd _ _)
  isLimit' := by
    constructor
    fapply PullbackCone.IsLimit.mk _
      (fun s => hpb.lift
        (s.fst ≫ f₃) (CartesianMonoidalCategory.lift s.fst s.snd) (by simp [s.condition]))
      (by
        intro s
        nth_rw 3 [← CartesianMonoidalCategory.lift_fst f₁ f₂]
        rw [IsPullback.lift_snd_assoc, CartesianMonoidalCategory.lift_fst])
      (by
        intro s
        simp only
        nth_rw 2 [← CartesianMonoidalCategory.lift_snd f₁ f₂]
        rw [IsPullback.lift_snd_assoc, CartesianMonoidalCategory.lift_snd])
      (by
        intro s m hm₁ hm₂
        apply hpb.hom_ext
        · rw [reassoc_of% hm₁]
          simp
        · rw [IsPullback.lift_snd]
          simp_all)

lemma IsPullback.pullback_fst_monoidal {A₁ A₂ A₃ B₁ B₂ B₃ Z₁ Z₂ : C}
    {f₁ : A₁ ⟶ Z₁} {f₂ : A₁ ⟶ A₂} {f₃ : Z₁ ⟶ A₃} {f₄ : A₂ ⟶ A₃} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : B₁ ⟶ Z₁} {g₂ : B₁ ⟶ B₂} {g₃ : Z₁ ⟶ B₃} {g₄ : B₂ ⟶ B₃} (hg : IsPullback g₁ g₂ g₃ g₄)
    {f' : Z₂ ⟶ A₁} {g' : Z₂ ⟶ B₁} (hf' : IsPullback f' g' f₁ g₁) :
    IsPullback (f' ≫ f₁)
      (CartesianMonoidalCategory.lift (f' ≫ f₂) (g' ≫ g₂))
      (CartesianMonoidalCategory.lift f₃ g₃)
      (f₄ ⊗ₘ g₄) := by
  convert hf'.pullback_monoidal.paste_vert (hf.tensor hg) <;> simp

lemma IsPullback.pullback_snd_monoidal {A₁ A₂ A₃ B₁ B₂ B₃ Z₁ Z₂ : C}
    {f₁ : A₁ ⟶ A₂} {f₂ : A₁ ⟶ Z₁} {f₃ : A₂ ⟶ A₃} {f₄ : Z₁ ⟶ A₃} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : B₁ ⟶ B₂} {g₂ : B₁ ⟶ Z₁} {g₃ : B₂ ⟶ B₃} {g₄ : Z₁ ⟶ B₃} (hg : IsPullback g₁ g₂ g₃ g₄)
    {f' : Z₂ ⟶ A₁} {g' : Z₂ ⟶ B₁} (hf' : IsPullback f' g' f₂ g₂) :
    IsPullback (CartesianMonoidalCategory.lift (f' ≫ f₁) (g' ≫ g₁))
      (f' ≫ f₂) (f₃ ⊗ₘ g₃)
      (CartesianMonoidalCategory.lift f₄ g₄) := by
  exact (hf.flip.pullback_fst_monoidal hg.flip hf').flip

open CartesianMonoidalCategory in
lemma IsPullback.graph {X Y : C} (f : X ⟶ Y) :
    IsPullback (CartesianMonoidalCategory.graph f) f (f ▷ Y)
      (CartesianMonoidalCategory.lift (𝟙 Y) (𝟙 Y)) := by
  refine IsPullback.of_isLimit' (by simp) (PullbackCone.IsLimit.mk _
    (fun s => s.fst ≫ fst _ _)
    (by
      intro s
      apply CartesianMonoidalCategory.hom_ext
      · simp
      simp only [CartesianMonoidalCategory.comp_lift, Category.comp_id, Category.assoc,
        CartesianMonoidalCategory.lift_snd]
      rw [← whiskerRight_fst,← whiskerRight_snd f, s.condition_assoc, s.condition_assoc,
        CartesianMonoidalCategory.lift_fst,CartesianMonoidalCategory.lift_snd])
      (by
        intro s
        simp only [Category.assoc]
        rw [← whiskerRight_fst,s.condition_assoc,
          CartesianMonoidalCategory.lift_fst,Category.comp_id])
      (by
        intro s m hm₁ _
        simp only [CartesianMonoidalCategory.comp_lift, Category.comp_id] at hm₁ ⊢
        rw [← hm₁]
        simp only [CartesianMonoidalCategory.lift_fst]))

lemma IsPullback.graph' {X Y : C} (f : X ⟶ Y) :
    IsPullback (CartesianMonoidalCategory.graph' f) f (Y ◁ f)
      (CartesianMonoidalCategory.lift (𝟙 Y) (𝟙 Y)) := by
  have := BraidedCategory.ofCartesianMonoidalCategory (C := C)
  have hf := IsPullback.graph f
  have := IsPullback.braiding_vert f (𝟙 Y)
  simp at this
  convert (hf.paste_horiz this.flip) <;> simp

section equalizer

lemma IsPullback.equalizer_monoidal {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g] :
    IsPullback (equalizer.ι f g) (equalizer.ι f g ≫ f)
      (CartesianMonoidalCategory.lift f g) (CartesianMonoidalCategory.lift (𝟙 Y) (𝟙 Y)) where
  w := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [equalizer.condition f g]
  isLimit' := by
    constructor
    refine PullbackCone.IsLimit.mk _ (fun s => (equalizer.lift s.fst ?_)) ?_ ?_ ?_
    · nth_rw 6 [← CartesianMonoidalCategory.lift_snd f g]
      nth_rw 4 [← CartesianMonoidalCategory.lift_fst f g]
      rw [s.condition_assoc, s.condition_assoc, CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.lift_snd]
    · intro s
      simp
    · intro s
      simp only [limit.lift_π_assoc, Fork.ofι_pt, parallelPair_obj_zero, Fork.ofι_π_app]
      nth_rw 4 [← CartesianMonoidalCategory.lift_fst f g]
      rw [s.condition_assoc,CartesianMonoidalCategory.lift_fst,Category.comp_id]
    · intro s m hm₁ hm₂
      apply equalizer.hom_ext
      simp [hm₁]

end equalizer
end CategoryTheory
