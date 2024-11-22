open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives using (Level; ℓ-zero; ℓ-suc)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep; funExtNonDep)
open import Cubical.Foundations.Function using (idfun; curry; uncurry)

open import Prelude

module IndexedContainers2 (I : Type) where

record IndexedContainer  : Type (ℓ-suc ℓ-zero) where
  field
    S : (i : I) → Type
    P : {i : I} → S i → (j : I) → Type

module _ where
  open IndexedContainer

  record _⇒_ (F G : IndexedContainer) : Type ℓ-zero where
    field
      smap : ∀ i → F .S i → G .S i
      pmap : ∀ {i} (s : F .S i) j → G .P (smap i s) j → F .P s j

  open _⇒_ public

  module _ {F G} {α β : F ⇒ G} where
    ⇒PathP :
      (≡smap : α .smap ≡ β .smap)
      (≡pmap : PathP (λ 𝒾 → ∀ {i} (s : F .S i) j → G .P (≡smap 𝒾 i s) j → F .P s j) (α .pmap) (β .pmap))
      → α ≡ β
    ⇒PathP ≡smap ≡pmap 𝒾 .smap = ≡smap 𝒾
    ⇒PathP ≡smap ≡pmap 𝒾 .pmap = ≡pmap 𝒾

    ⇒PathP-ext :
      (≡smap : ∀ {i} s → α .smap i s ≡ β .smap i s)
      (≡pmap : ∀ (i : I) s j
        → {p₁ : G .P (α .smap i s) j} {p₂ : G .P (β .smap i s) j}
          (p≡ : p₁ ≡[ ≡smap s , (λ s′ → G .P s′ j) ] p₂)
        → (α .pmap s j p₁) ≡ (β .pmap s j p₂))
      → α ≡ β
    ⇒PathP-ext ≡smap ≡pmap = ⇒PathP
      (funExt₂ λ _ s → ≡smap s)
      (implicitFunExt λ {i} → funExt₂ λ s j → funExtNonDep (≡pmap i s j))

    ⇒PathP-ext′ :
      (≡smap : ∀ {i} s → α .smap i s ≡ β .smap i s)
      (≡pmap : ∀ (i : I) s j
        → (pp : ∀ ι → G .P (≡smap s ι) j)
        → {p₁ : G .P (α .smap i s) j} {p₂ : G .P (β .smap i s) j}
          (p≡ : p₁ ≡[ ≡smap s , (λ s′ → G .P s′ j) ] p₂)
        → (α .pmap s j p₁) ≡ (β .pmap s j p₂))
      → α ≡ β
    ⇒PathP-ext′ ≡smap ≡pmap = ⇒PathP
      (funExt₂ λ _ s → ≡smap s)
      (implicitFunExt λ {i} → funExt₂ λ s j → {! !})
    
    eq? : (A B : Type) (C : B → Type) (D : A → Type)
      (f : A → B) 
      (h : (a : A) → C (f a) → D a)
      (g : A → B)
      (f≡g : f ≡ g) 
      (k : (a : A) → C (g a) → D a)
      (h≈k : ∀ x y → h x y ≡ k x (subst C (funExt⁻ f≡g x) y))
      → subst (λ f → (a : A) → C (f a) → D a) f≡g h ≡ k 
    eq? A B C D f h g =
        J
          (λ g f≡g → (k : (a : A) → C (g a) → D a)
            (h≈k : ∀ x y → h x y ≡ k x (subst C (funExt⁻ f≡g x) y))
            → subst (λ f → (a : A) → C (f a) → D a) f≡g h ≡ k) 
        aux {g}
      where
      aux : (k : (a : A) → C (f a) → D a)
        → ((x : A) (y : C (f x)) → h x y ≡ k x (subst C refl y))
        → subst (λ f₁ → (a : A) → C (f₁ a) → D a) refl h ≡ k
      aux k h≈k =
        subst (_≡ k) (sym $ substRefl h) (funExt₂ h≈k′)  
        where
        h≈k′ : (x : A) (y : C (f x)) → h x y ≡ k x y
        h≈k′ x y = subst (λ z → h x y ≡ k x z) (substRefl y) $ h≈k x y

    -- ⇒PathP-ext′ :
    --   (≡smap : ∀ {i} s → α .smap i s ≡ β .smap i s)
    --   (≡pmap : ∀ (i : I) s j
    --     (p : G .P (α .smap i s) j)
    --     → (α .pmap s j p) ≡ (β .pmap s j (subst (λ s → G .P s j) (≡smap s) p)))
    --   → α ≡ β
    -- ⇒PathP-ext′ ≡smap ≡pmap = ⇒PathP
    --   (funExt₂ λ _ s → ≡smap s)
    --   (implicitFunExt λ {i} → funExt₂ λ s j → funExtDep λ { p≡ → toPathP {! !} })
    --
    -- ⇒PathP-ext″ :
    --   (≡smap : ∀ {i} s → α .smap i s ≡ β .smap i s)
    --   (≡pmap : ∀ (i : I) s j
    --     (p : G .P (β .smap i s) j)
    --     → (α .pmap s j (subst (λ s → G .P s j) (sym $ ≡smap s) p)) ≡ (β .pmap s j p))
    --   → α ≡ β
    -- ⇒PathP-ext″ ≡smap ≡pmap = ⇒PathP
    --   (funExt₂ λ _ s → ≡smap s)
    --   (implicitFunExt λ {i} → funExt₂ λ s j → funExtDep λ { {x₀ = p₁} {x₁ = p₂} p≡ → toPathP {! ≡pmap i s j p₂ !} })

  idᶜ : IndexedContainer
  idᶜ .S _ = Unit
  idᶜ .P {i} _ j = i ≡ j

  module _ {F} where
    id₁ : F ⇒ F 
    id₁ .smap _ s = s
    id₁ .pmap s j p = p

  module _ (F : IndexedContainer) where
    ⟦_⟧ : (I → Type) → (I → Type)
    ⟦_⟧ X i = Σ[ s ∈ F .S i ] (∀ {j} (p : F .P s j) → X j)

    _⟨$⟩_ : {X Y : I → Type} → (∀ i → X i → Y i) → (∀ i → ⟦_⟧ X i → ⟦_⟧ Y i)
    _⟨$⟩_ f i (s , v) .fst = s
    _⟨$⟩_ f i (s , v) .snd {j} p = f j (v p)

  module _ (F G : IndexedContainer) where
    _;_ : IndexedContainer
    _;_ .S = ⟦ G ⟧ (F .S) 
    _;_ .P (s , v) k = Σ[ j ∈ I ] Σ[ p ∈ G .P s j ] F .P (v p) k

    -- interpretation is strong monoidal
    module _ (X : I → Type) (i : I) where
      ;-≃ : ∀ i → ⟦ G ⟧ (⟦ F ⟧ X) i ≃ ⟦ _;_ ⟧ X i
      ;-≃ i = isoToEquiv ;-iso where
        open Iso
        ;-iso : Iso (⟦ G ⟧ (⟦ F ⟧ X) i) (⟦ _;_ ⟧ X i)
        -- ;-iso .fun (s′ , br) = (s′ , λ j p → br j p .fst) , λ { k (j , (p′ , p)) → br j p′ .snd k p }
        ;-iso .fun (s′ , br) = {! !}
        -- ;-iso .inv ((s′ , br) , ;ops) = s′ , λ { j p′ → br j p′ , λ { k p → ;ops k (j , p′ , p) } }
        ;-iso .inv ((s′ , br) , ;ops) = {! !}
        ;-iso .rightInv _ = refl
        ;-iso .leftInv _ = refl

module _ {F G H K} where
  _;ₕ_ : (α : F ⇒ H) (β : G ⇒ K) → (F ; G) ⇒ (H ; K)
  (α ;ₕ β) .smap _ (Gs , Gsp→Fs) = β .smap _ Gs , λ { {j} Ksp → α .smap j (Gsp→Fs (β .pmap Gs j Ksp)) }
  (α ;ₕ β) .pmap {i} (Gs , Gsp→Fs) j (i′ , Kp , Hp) = let
      Gsp = β .pmap Gs i′ Kp 
    in i′ , Gsp , α .pmap (Gsp→Fs Gsp) j Hp

module _ {F G H} where
  _;ᵥ_ : (α : F ⇒ G) (β : G ⇒ H) → (F ⇒ H)
  (α ;ᵥ β) .smap _ s = β .smap _ (α .smap _ s)
  (α ;ᵥ β) .pmap s _ p = α .pmap s _ (β .pmap (α .smap _ s) _ p)

module _ {F G} where
  id₁-;ₕ : id₁ {F} ;ₕ id₁ {G} ≡ id₁ {F ; G}
  id₁-;ₕ = ⇒PathP
    (λ i j p → p)
    λ i {k} s j p → p

module _ {F G} (α : F ⇒ G) where
  record ⇒Iso : Type ℓ-zero where
    field
      inv : G ⇒ F
      inv-l : α ;ᵥ inv ≡ id₁
      inv-r : inv ;ᵥ α ≡ id₁

module _ {F} where

  open IndexedContainer F

  open ⇒Iso

  unitor-l : (idᶜ ; F) ⇒ F
  unitor-l .smap _ (s , _) = s
  unitor-l .pmap {i} (s , _) j p = j , p , refl

  unitor-l-inv : F ⇒ (idᶜ ; F)
  unitor-l-inv .smap i s = s , _
  unitor-l-inv .pmap s j (k , p , k≡j) = subst (P s) k≡j p

  unitor-l-iso : ⇒Iso unitor-l
  unitor-l-iso .inv = unitor-l-inv
  unitor-l-iso .inv-l = ⇒PathP-ext
    (λ { (s , _) → ΣPathP ({! !} , {! !}) })
    {! !}
  unitor-l-iso .inv-r = {! !}


  unitor-r : (F ; idᶜ) ⇒ F
  unitor-r .smap i (_ , si) = si refl
  unitor-r .pmap {i} (_ , si) j p = i , refl , p

module _ {F G H} where
  associator : (F ; (G ; H)) ⇒ ((F ; G) ; H)
  associator .smap _ ((s″ , op″) , op′) = s″ , λ {j} p″ → op″ p″ , λ p′ → op′ (j , p″ , p′)
  associator .pmap ((s″ , op″) , op′) j′  (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p

_² : IndexedContainer → IndexedContainer
IC ² = IC ; IC

module _ (T : IndexedContainer) where 
  open IndexedContainer T

  ΣP : {i : I} → S i → Type
  ΣP s = Σ I (P s)

  record RawICMonoid : Type ℓ-zero where
    field
      η : idᶜ ⇒ T
      μ : (T ²) ⇒ T

  record is-ICMonoid (raw : RawICMonoid) : Type ℓ-zero where
    open RawICMonoid raw
    field
      η-unit-l : (η ;ₕ id₁) ;ᵥ μ ≡ unitor-l
      η-unit-r : (id₁ {F = T} ;ₕ η) ;ᵥ μ ≡ unitor-r
      μ-assoc : (id₁ {F = T} ;ₕ μ) ;ᵥ μ ≡ (associator {F = T} ;ᵥ ((μ ;ₕ id₁) ;ᵥ μ))

  record ICMS : Type ℓ-zero where
    field
      e  : ∀ i → S i
      _•_ : ∀ {i} (s : S i)
        → (v : ∀ {j} (p : P s j) → S j)
        → S i
      _↑_ : ∀ {i} {s : S i}
        → (v : ∀ {j} (p : P s j) → S j)
        → {j : I} (p : P (s • v) j)
        → I 
      _↖_ : ∀ {i} {s : S i}
        → (v : ∀ {j} (p : P s j) → S j)
        → {j : I} (p : P (s • v) j)
        → P s (v ↑ p)
      _↗_ : ∀ {i} {s : S i}
        → (v : ∀ {j} (p : P s j) → S j)
        → {j : I} (p : P (s • v) j)
        → P (v (v ↖ p)) j
      P-e-idx : ∀ {i} {j} → P (e i) j → i ≡ j
--       e-unit-r : ∀ {i} (u : ∀ j → S j) → (e i • (λ p → u (p .fst))) ≡ u i
      e-unit-l : ∀ {i} (s : S i) → s • (λ {j} _ → e j) ≡ s 
      ↑-unit-l : ∀ {i} {s : S i} {j}
        → (p : P s j)  
        → ((λ {j} _ → e j) ↑ (subst (λ s → P s j) (sym $ e-unit-l s) p)) ≡ j
--       -- e-act-l₁ : ∀ i (v : ∀ i′ → S i′) j (p : P (v i) j)
--       --   → ((λ j _ → v j) ↖ subst (λ s → P s j) (sym (e-unit-l i v)) p) .fst ≡ i
--       -- e-act-l₂ : ∀ i (v : ∀ i′ → S i′) j (p : P (v i) j)
--       --   → (λ j _ → v j) ↗ subst (λ s → P s j) (sym (e-unit-l i v)) p ≡ subst (λ i → P (v i) j) {! !} p
--       e-act-l : {! !}
--       e-act-r : {! !}
--
--       •-assoc : ∀ i 
--         (s : S i)
--         (v : ∀ (p : ΣP s) → S (p .fst))
--         (w : ∀ (p : ΣP s) (p′ : ΣP (v p)) → S (p′ .fst))
--         → ((s • v) • λ p → w (v ↖ p) (p .fst , (v ↗ p))) ≡ s • (λ p → v p • w p) 
--       ↖↖-↖ : ∀ i 
--         (s : S i)
--         (v : ∀ (p : ΣP s) → S (p .fst))
--         (w : ∀ (p : ΣP s) (p′ : ΣP (v p)) → S (p′ .fst))
--         (p : ΣP (s • (λ p → v p • w p)))
--         → {! ? ↖ (? ↖ p) !} ≡ (λ p → v p • w p) ↖ p
--
--
--
  module _ (icms : ICMS) where
    open ICMS icms
    open RawICMonoid

    ICMS→RawICMonoid : RawICMonoid
    ICMS→RawICMonoid .η .smap i _ = e i
    ICMS→RawICMonoid .η .pmap _ j p = P-e-idx p
    ICMS→RawICMonoid .μ .smap i (s , v) = s • v
    ICMS→RawICMonoid .μ .pmap (s , v) j p = v ↑ p , v ↖ p , v ↗ p

    open is-ICMonoid

    ICMS→is-ICMonoid : is-ICMonoid ICMS→RawICMonoid
    ICMS→is-ICMonoid .η-unit-l = 
      {! !}
      -- ⇒PathP-ext″
      --   (λ { (s , _) → e-unit-l s })
      --   λ { i (s , v) j p → ΣPathP (
      --     ↑-unit-l p , ΣPathP (
      --       {! !} , {! !}
      --     )
      --   ) }
      -- ⇒PathP-ext
      --   (λ { (s , _) → e-unit-l s} )
      --   λ { i (s , v) j {p₁} {p₂} p≡ → ΣPathP (
      --     {! ↑-unit-l p₁!}
      --     , {! !}
      --   ) }
    ICMS→is-ICMonoid .η-unit-r = {! !}
    ICMS→is-ICMonoid .μ-assoc  = {! !}

  module _ (icmon : RawICMonoid) where
    open ICMS
    open RawICMonoid icmon

    -- RawICMonoid→ICMS : ICMS
    -- RawICMonoid→ICMS .e i = η .smap i _
    -- RawICMonoid→ICMS ._•_ {i} s v = μ .smap i (s , curry v)
    -- RawICMonoid→ICMS ._↖_ {s} v {j} p = 
    --  let
    --   k , p′ , _ = μ .pmap (s , curry v) j p
    --  in k , p′
    -- RawICMonoid→ICMS ._↗_ {s} v {j} p = μ .pmap (s , curry v) j p .snd .snd
    -- RawICMonoid→ICMS .P-e-idx {j} p = η .pmap _ j p
