import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory Limits

variable {C : Type*} [Category C]

/-
The below lemma is relevant to Topos theory, as in the context of a topos, the below helps define
the intersection morphism ⊓ : Ω ⨯ Ω ⟶ Ω which induces and characterizes all intersections of
subobjects (which are pullbacks) The morphism is defined as the classifier of
`⟨truth,truth⟩ : (Ω₀ ⨯ Ω₀) ⟶ (Ω ⨯ Ω)`.
In order to show that indeed for subobjects `f,g` of `X`, we have that `χ (f ⊓ g) = ⊓ ≫ ⟨χ f,χ g⟩`,
we need to show the large square in the following diagram is a pullback:
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

lemma CategoryTheory.IsPullback.shift_mono_left {X₁ X₂ X₃ X₃' X₄ : C} {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃}
    (f₂' : X₃ ⟶ X₃') [Mono f₂'] {f₃ : X₂ ⟶ X₄} {f₄ : X₃' ⟶ X₄}
    (hf : IsPullback f₁ (f₂ ≫ f₂') f₃ f₄) :
    IsPullback f₁ f₂ f₃ (f₂' ≫ f₄) := by
  refine { toCommSq.w := ?_, isLimit' := ⟨?_⟩ }
  · simpa using hf.w
  · refine PullbackCone.IsLimit.mk _ (fun s => hf.lift s.fst (s.snd ≫ f₂') ?_) (by simp) ?_ ?_
    · rw [s.condition,Category.assoc]
    · intro s
      simp only
      apply Mono.right_cancellation (f := f₂')
      rw [Category.assoc, hf.lift_snd]
    · intro s m hm₁ hm₂
      apply hf.hom_ext
      · rw [hm₁,hf.lift_fst]
      · rw [reassoc_of% hm₂,hf.lift_snd]

lemma CategoryTheory.IsPullback.shift_mono_top {X₁ X₂ X₂' X₃ X₄ : C} {f₁ : X₁ ⟶ X₂}
    (f₁' : X₂ ⟶ X₂') [Mono f₁'] {f₂ : X₁ ⟶ X₃}
    {f₃ : X₂' ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback (f₁ ≫ f₁') f₂ f₃ f₄) :
    IsPullback f₁ f₂ (f₁' ≫ f₃) f₄ := by
  exact hf.flip.shift_mono_left.flip

/--
If all small squares but the top left are pullback squares, the top left square commutes,
and the full square is a pullback, then the top left square is a pullback too.
Variables are named according to the following diagram:
```
X₁ -f₁→ X₂ -f₂→ X₃
| hf_tl | hf_tr |
f₃      f₄      f₅
↓       ↓       ↓
X₄ -f₆→ X₅ -f₇→ X₆
| hf_bl | hf_br |
f₈      f₉      f₁₀
↓       ↓       ↓
X₇-f₁₁→ X₈-f₁₂→ X₉
```
-/
lemma CategoryTheory.IsPullback.of_bot_right {X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
    {f₃ : X₁ ⟶ X₄} {f₄ : X₂ ⟶ X₅} {f₅ : X₃ ⟶ X₆}
    {f₆ : X₄ ⟶ X₅} {f₇ : X₅ ⟶ X₆}
    {f₈ : X₄ ⟶ X₇} {f₉ : X₅ ⟶ X₈} {f₁₀ : X₆ ⟶ X₉}
    {f₁₁ : X₇ ⟶ X₈} {f₁₂ : X₈ ⟶ X₉}
    (hf : IsPullback (f₁ ≫ f₂) (f₃ ≫ f₈) (f₅ ≫ f₁₀) (f₁₁ ≫ f₁₂))
    (hf_tl : CommSq f₁ f₃ f₄ f₆) (hf_tr : IsPullback f₂ f₄ f₅ f₇)
    (hf_bl : IsPullback f₆ f₈ f₉ f₁₁) (hf_br : IsPullback f₇ f₉ f₁₀ f₁₂) :
    IsPullback f₁ f₃ f₄ f₆ :=
    (hf.of_bot (hf_tl.horiz_comp hf_tr.toCommSq).w (hf_bl.paste_horiz hf_br)).of_right
    hf_tl.w hf_tr

lemma CategoryTheory.IsPullback.of_comp_of_mono {X₁ X₂ X₃ X₄ Z : C} {f₁ : X₁ ⟶ X₂}
    {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄}
    (g : X₄ ⟶ Z) [Mono g]
    (hf : IsPullback f₁ f₂ (f₃ ≫ g) (f₄ ≫ g)) : IsPullback f₁ f₂ f₃ f₄ := by
  have hpb: IsPullback (f₁ ≫ 𝟙 _) (f₂ ≫ 𝟙 _) (f₃ ≫ g) (f₄ ≫ g) := by
    convert hf <;> simp
  have hf' : CommSq f₁ f₂ f₃ f₄ := ⟨Mono.right_cancellation _ _ (by simpa using hf.w)⟩
  exact hpb.of_bot_right hf' (.id_horiz f₃) (.id_vert f₄) (.of_horiz_isIso_mono (by simp))
