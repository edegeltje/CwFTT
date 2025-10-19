import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory Limits

variable {C : Type*} [Category C]

/-
The below lemma is relevant to Topos theory, as in the context of a topos, the below helps define the intersection morphism ⊓ : Ω ⨯ Ω ⟶ Ω which induces and characterizes all intersections of subobjects (which are pullbacks)
The morphism is defined as the classifier of ⟨truth,truth⟩ : (Ω₀ ⨯ Ω₀) ⟶ (Ω ⨯ Ω).
In order to show that indeed for subobjects `f,g` of `X`, we have that χ (f ⊓ g) = ⊓ ≫ ⟨χ f,χ g⟩, we need to show the large square in the following diagram is a pullback:
 (f ⊓ g)  →    Z

    ↓          ↓

    ⟨truth,truth⟩
(Ω₀ ⨯ Ω₀) → (Ω × Ω)

    ↓          ↓ (⊓)

    Ω₀ -truth→ Ω
for which it suffices to show that the top and bottom diagrams are both pullbacks.

-/

/--
Given two pullbacksquares
A₁ -f₁→ Z    B₁ -g₁→ Z

↓f₂     ↓f₃  ↓g₂     ↓g₃

A₂ -f₄→ A₃   B₂ -g₄→ B₃
, we get a new pullbacksquare
(A₁ ⨯[Z] B₁) → (Z)
     ↓          ↓
 (A₂ × B₂) → (A₃ × B₃)

where the top morphism is the diagonal of the pullback
(A₁ ⨯[Z] B₁) → A₁
    ↓          ↓
    B₁       → Z
-/

lemma CategoryTheory.IsPullback.pullback {X₁ X₂ X₃ X₄ : C} [HasBinaryProduct X₂ X₃]
    [HasBinaryProduct X₄ X₄] {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃}
    {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄) :
    IsPullback (f₁ ≫ f₃)
      (Limits.prod.lift f₁ f₂) (Limits.diag X₄)
      (Limits.prod.map f₃ f₄) := by
  refine ⟨⟨?_⟩,⟨?_⟩⟩
  · apply Limits.prod.hom_ext
    · cat_disch
    · simp [hf.w]
  · refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro s
      refine hf.lift (s.snd ≫ Limits.prod.fst) (s.snd ≫ Limits.prod.snd) ?_
      have := s.condition
      simp only [prod.comp_lift, Category.comp_id, Limits.prod.hom_ext_iff, limit.lift_π,
        BinaryFan.mk_pt, BinaryFan.mk_fst, Category.assoc, prod.map_fst, BinaryFan.mk_snd,
        prod.map_snd] at this
      simp [this.left, ← this.right]
    · intro s
      simp only [lift_fst_assoc, Category.assoc]
      have := s.condition
      simp [Limits.prod.hom_ext_iff] at this
      exact this.left.symm
    · cat_disch
    · intro s m hm₁ hm₂
      simp [Limits.prod.hom_ext_iff] at hm₂ ⊢
      apply hf.hom_ext
      -- apply Limits.prod.hom_ext
      · simpa using hm₂.left
      · simpa [hm₁] using hm₂.right

lemma CategoryTheory.IsPullback.prod {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    [HasBinaryProduct X₁ Y₁] [HasBinaryProduct X₂ Y₂]
    [HasBinaryProduct X₃ Y₃] [HasBinaryProduct X₄ Y₄]
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₁ ⟶ Y₃} {g₃ : Y₂ ⟶ Y₄} {g₄ : Y₃ ⟶ Y₄} (hg : IsPullback g₁ g₂ g₃ g₄) :
    IsPullback (prod.map f₁ g₁) (prod.map f₂ g₂) (prod.map f₃ g₃) (prod.map f₄ g₄) := by
  refine ⟨⟨?_⟩,⟨?_⟩⟩
  · simp [hf.w,hg.w]
  · refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro s
      have := s.condition
      simp only [Limits.prod.hom_ext_iff, Category.assoc, prod.map_fst, prod.map_snd] at this
      apply prod.lift
      · fapply hf.lift (s.fst ≫ prod.fst) (s.snd ≫ prod.fst)
        simpa using this.left
      · fapply hg.lift (s.fst ≫ prod.snd) (s.snd ≫ prod.snd)
        simpa using this.right
    · intro s
      simp [Limits.prod.hom_ext_iff]
    · intro s
      simp [Limits.prod.hom_ext_iff]
    · intro s m hm₁ hm₂
      simp_all [Limits.prod.hom_ext_iff]
      constructor
      · apply hf.hom_ext
        · simpa using hm₁.left
        · simpa using hm₂.left
      · apply hg.hom_ext
        · simpa using hm₁.right
        · simpa using hm₂.right
    -- all_goals sorry

lemma CategoryTheory.IsPullback.pullback_fst {C : Type*} [Category C] {A₁ A₂ A₃ B₁ B₂ B₃ Z₁ Z₂ : C}
    {f₁ : A₁ ⟶ Z₁} {f₂ : A₁ ⟶ A₂} {f₃ : Z₁ ⟶ A₃} {f₄ : A₂ ⟶ A₃} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : B₁ ⟶ Z₁} {g₂ : B₁ ⟶ B₂} {g₃ : Z₁ ⟶ B₃} {g₄ : B₂ ⟶ B₃} (hg : IsPullback g₁ g₂ g₃ g₄)
    [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂] [HasBinaryProduct A₃ B₃]
    [HasBinaryProduct Z₁ Z₁] {f' : Z₂ ⟶ A₁} {g' : Z₂ ⟶ B₁} (hf' : IsPullback f' g' f₁ g₁) :
    IsPullback (f' ≫ f₁)
      (Limits.prod.lift (f' ≫ f₂) (g' ≫ g₂))
      (Limits.prod.lift f₃ g₃)
      (Limits.prod.map f₄ g₄) := by
    convert hf'.pullback.paste_vert (hf.prod hg) <;> simp

lemma CategoryTheory.IsPullback.pullback_snd {A₁ A₂ A₃ B₁ B₂ B₃ Z₁ Z₂ : C}
    {f₁ : A₁ ⟶ A₂} {f₂ : A₁ ⟶ Z₁} {f₃ : A₂ ⟶ A₃} {f₄ : Z₁ ⟶ A₃} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : B₁ ⟶ B₂} {g₂ : B₁ ⟶ Z₁} {g₃ : B₂ ⟶ B₃} {g₄ : Z₁ ⟶ B₃} (hg : IsPullback g₁ g₂ g₃ g₄)
    [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂] [HasBinaryProduct A₃ B₃]
    [HasBinaryProduct Z₁ Z₁] {f' : Z₂ ⟶ A₁} {g' : Z₂ ⟶ B₁} (hf' : IsPullback f' g' f₂ g₂) :
    IsPullback (prod.lift (f' ≫ f₁) (g' ≫ g₁))
      (f' ≫ f₂) (prod.map f₃ g₃)
      (prod.lift f₄ g₄) := by
  exact (hf.flip.pullback_fst hg.flip hf').flip

lemma CategoryTheory.IsPullback.mono_fst {X₁ X₂ X₃ X₄ : C} {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃}
    {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄) [Mono f₄] : Mono f₁ := by
  constructor
  intro Y f g heq
  apply hf.hom_ext heq
  rw [← cancel_mono f₄]
  simp [← hf.w,reassoc_of% heq]

lemma CategoryTheory.IsPullback.mono_snd {X₁ X₂ X₃ X₄ : C} {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃}
    {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄) [Mono f₃] : Mono f₂ :=
  hf.flip.mono_fst
