import CwFTT.Util.Cartesian
import CwFTT.Util.Pullback

universe v u
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
open Limits MonoidalCategory CartesianMonoidalCategory

lemma _root_.CategoryTheory.IsPullback.tensor {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₁ ⟶ Y₃} {g₃ : Y₂ ⟶ Y₄} {g₄ : Y₃ ⟶ Y₄} (hg : IsPullback g₁ g₂ g₃ g₄) :
    IsPullback (tensorHom f₁ g₁) (tensorHom f₂ g₂) (tensorHom f₃ g₃) (tensorHom f₄ g₄) := by
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

open MonoidalCategory

lemma IsPullback.pullback_monoidal {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃}
    {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄) :
    IsPullback (f₁ ≫ f₃)
      (CartesianMonoidalCategory.lift f₁ f₂) (CartesianMonoidalCategory.lift (𝟙 X₄) (𝟙 _))
      (f₃ ⊗ₘ f₄) := by
  refine ⟨⟨?_⟩,⟨?_⟩⟩
  · apply CartesianMonoidalCategory.hom_ext_iff.mpr
    simp [hf.w]
  · refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro s
      refine hf.lift (s.snd ≫ fst _ _) (s.snd ≫ snd _ _) ?_
      have := s.condition
      simp only [comp_lift, Category.comp_id, CartesianMonoidalCategory.hom_ext_iff,
        CartesianMonoidalCategory.lift_fst, Category.assoc, tensorHom_fst,
        CartesianMonoidalCategory.lift_snd, tensorHom_snd] at this
      simp [this.left, ← this.right]
    · intro s
      simp only [IsPullback.lift_fst_assoc, Category.assoc]
      have := s.condition
      simp [CartesianMonoidalCategory.hom_ext_iff] at this
      exact this.left.symm
    · cat_disch
    · intro s m hm₁ hm₂
      simp only [comp_lift, CartesianMonoidalCategory.hom_ext_iff,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd] at hm₂ ⊢
      apply hf.hom_ext
      -- apply Limits.prod.hom_ext
      · simpa using hm₂.left
      · simpa [hm₁] using hm₂.right

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



end CategoryTheory
