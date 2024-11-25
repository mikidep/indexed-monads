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

module IndexedMonads (I : Type) where

record IndexedContainer  : Type (ℓ-suc ℓ-zero) where
  field
    S : (i : I) → Type
    P : {i : I} → S i → (j : I) → Type

module _ where
  open IndexedContainer

  record _⇒_ (F G : IndexedContainer) : Type ℓ-zero where
    field
      σ : ∀ {i} → F .S i → G .S i
      π : ∀ {i} (s : F .S i) {j} → G .P (σ s) j → F .P s j

  open _⇒_ public

  module _ {F G} {α β : F ⇒ G} where
    ⇒PathP :
      (≡σ : (λ {i} → α .σ {i}) ≡ β .σ)
      (≡π : PathP (λ ι → ∀ {i} s {j} → G .P (≡σ ι s) j → F .P s j) (λ {i} → α .π {i}) (β .π))
      → α ≡ β
    ⇒PathP ≡σ ≡π 𝒾 .σ = ≡σ 𝒾
    ⇒PathP ≡σ ≡π 𝒾 .π = ≡π 𝒾

    ⇒PathP-ext :
      (≡σ : ∀ {i} s → α .σ s ≡ β .σ s)
      (≡π : ∀ (i : I) s j
        → {p₁ : G .P (α .σ s) j} {p₂ : G .P (β .σ s) j}
          (p≡ : p₁ ≡[ ≡σ s , (λ s′ → G .P s′ j) ] p₂)
        → (α .π s p₁) ≡ (β .π s p₂))
      → α ≡ β
    ⇒PathP-ext ≡σ ≡π = ⇒PathP
      (implicitFunExt λ {i} → funExt ≡σ)
      (implicitFunExt λ {i} → funExt λ s → implicitFunExt λ {j} → funExtNonDep (≡π i s j))

    lemma : {A B : Type} {C : B → Type} {D : A → Type}
      (f : A → B) 
      (h : (a : A) → C (f a) → D a)
      (g : A → B)
      (f≡g : f ≡ g) 
      (k : (a : A) → C (g a) → D a)
      (h≈k : ∀ x y → h x y ≡ k x (subst C (funExt⁻ f≡g x) y))
      → subst (λ f → (a : A) → C (f a) → D a) f≡g h ≡ k 
    lemma {A} {B} {C} {D} f h g =
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

    ⇒PathP-ext′ :
      (≡σ : ∀ {i} (s : F .S i) → α .σ s ≡ β .σ s)
      (≡π : ∀ {i} (s : F .S i) {j} (p : G .P _ j) → α .π s p ≡ β .π s (subst (λ s → G .P s j) (≡σ s) p))
      → α ≡ β
      -- TODO: improve statement as formulated in eq?
    ⇒PathP-ext′ ≡σ ≡π = {! !}
    
  idᶜ : IndexedContainer
  idᶜ .S _ = Unit
  idᶜ .P {i} _ j = i ≡ j

  module _ {F} where
    id₁ : F ⇒ F 
    id₁ .σ s = s
    id₁ .π s p = p

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
    -- module _ (X : I → Type) (i : I) where
    --   ;-≃ : ∀ i → ⟦ G ⟧ (⟦ F ⟧ X) i ≃ ⟦ _;_ ⟧ X i
    --   ;-≃ i = isoToEquiv ;-iso where
    --     open Iso
    --     ;-iso : Iso (⟦ G ⟧ (⟦ F ⟧ X) i) (⟦ _;_ ⟧ X i)
    --     -- ;-iso .fun (s′ , br) = (s′ , λ j p → br j p .fst) , λ { k (j , (p′ , p)) → br j p′ .snd k p }
    --     ;-iso .fun (s′ , br) = {! !}
    --     -- ;-iso .inv ((s′ , br) , ;ops) = s′ , λ { j p′ → br j p′ , λ { k p → ;ops k (j , p′ , p) } }
    --     ;-iso .inv ((s′ , br) , ;ops) = {! !}
    --     ;-iso .rightInv _ = refl
    --     ;-iso .leftInv _ = refl

module _ {F G H K} where
  _;ₕ_ : (α : F ⇒ H) (β : G ⇒ K) → (F ; G) ⇒ (H ; K)
  (α ;ₕ β) .σ (Gs , Gsp→Fs) = β .σ Gs , λ { {j} Ksp → α .σ (Gsp→Fs (β .π Gs Ksp)) }
  (α ;ₕ β) .π {i} (Gs , Gsp→Fs) (i′ , Kp , Hp) = let
      Gsp = β .π Gs Kp 
    in i′ , Gsp , α .π (Gsp→Fs Gsp) Hp

module _ {F G H} where
  _;ᵥ_ : (α : F ⇒ G) (β : G ⇒ H) → (F ⇒ H)
  (α ;ᵥ β) .σ s = β .σ (α .σ s)
  (α ;ᵥ β) .π s p = α .π s (β .π (α .σ s) p)

-- module _ {F G} where
--   id₁-;ₕ : id₁ {F} ;ₕ id₁ {G} ≡ id₁ {F ; G}
--   id₁-;ₕ = ⇒PathP-ext′
--     (λ { s → refl })
--     (λ { s p → sym $ substRefl p })
--
-- -- module _ {F G} (α : F ⇒ G) where
--   record ⇒Iso : Type ℓ-zero where
--     field
--       inv : G ⇒ F
--       inv-l : α ;ᵥ inv ≡ id₁
--       inv-r : inv ;ᵥ α ≡ id₁
--
module _ {F} where

  open IndexedContainer F

  -- open ⇒Iso

  unitor-l : (idᶜ ; F) ⇒ F
  unitor-l .σ (s , _) = s
  unitor-l .π {i} (s , _) {j} p = j , p , refl

  -- unitor-l-inv : F ⇒ (idᶜ ; F)
  -- unitor-l-inv .σ s = s , _
  -- unitor-l-inv .π s (k , p , k≡j) = subst (P s) k≡j p
  --
  -- unitor-l-iso : ⇒Iso unitor-l
  -- unitor-l-iso .inv = unitor-l-inv
  -- unitor-l-iso .inv-l = ⇒PathP-ext′
  --   (λ { s → refl })
  --   λ { s p → sym $ substRefl p }
  -- unitor-l-iso .inv-r = {! !}


  unitor-r : (F ; idᶜ) ⇒ F
  unitor-r .σ (_ , si) = si refl
  unitor-r .π {i} (_ , si) p = i , refl , p

module _ {F G H} where
  associator : (F ; (G ; H)) ⇒ ((F ; G) ; H)
  associator .σ ((s″ , op″) , op′) = s″ , λ {j} p″ → op″ p″ , λ p′ → op′ (j , p″ , p′)
  associator .π ((s″ , op″) , op′) (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p

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
      e-unit-l : ∀ {i} (s : S i) → s • (λ {j} _ → e j) ≡ s 
      ↑-unit-l : ∀ {i} {s : S i} {j}
        → (p : P (s • (λ {j} _ → e j)) j)  
        → (λ {j} _ → e j) ↑ p ≡ j
      ↖-unit-l : ∀ {i} {s : S i} {j}
        → (p : P (s • (λ {j} _ → e j)) j)  
        → let
            tr₁ = subst (P s) (↑-unit-l p)
            tr₂ = subst (λ s → P s _) (e-unit-l s)
          in
            tr₁ $ (λ {j} _ → e j) ↖ p ≡ tr₂ $ p
      ↗-unit-l : ∀ {i} {s : S i} {j}
        → (p : P (s • (λ {j} _ → e j)) j)  
        → let
            tr = subst (_≡ j) (↑-unit-l p)
          in
            tr $ P-e-idx ((λ {j} _ → e j) ↗ p) ≡ refl
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
    ICMS→RawICMonoid .η .σ {i} _ = e i
    ICMS→RawICMonoid .η .π _ p = P-e-idx p
    ICMS→RawICMonoid .μ .σ (s , v) = s • v
    ICMS→RawICMonoid .μ .π (s , v) p = v ↑ p , v ↖ p , v ↗ p

    open is-ICMonoid

    ICMS→is-ICMonoid : is-ICMonoid ICMS→RawICMonoid
    ICMS→is-ICMonoid .η-unit-l = ⇒PathP-ext′
      (λ { (s , v) → e-unit-l s })
      λ { (s , v) {j} p → ΣPathP
        ( ↑-unit-l p
        , ΣPathP 
          ( toPathP (↖-unit-l p)
          , toPathP (↗-unit-l p)
          )
        )
      }
    ICMS→is-ICMonoid .η-unit-r = {! !}
    ICMS→is-ICMonoid .μ-assoc  = {! !}

  module _ (icmon : RawICMonoid) where
    open ICMS
    open RawICMonoid icmon

    -- RawICMonoid→ICMS : ICMS
    -- RawICMonoid→ICMS .e i = η .σ i _
    -- RawICMonoid→ICMS ._•_ {i} s v = μ .σ i (s , curry v)
    -- RawICMonoid→ICMS ._↖_ {s} v {j} p = 
    --  let
    --   k , p′ , _ = μ .π (s , curry v) j p
    --  in k , p′
    -- RawICMonoid→ICMS ._↗_ {s} v {j} p = μ .π (s , curry v) j p .snd .snd
    -- RawICMonoid→ICMS .P-e-idx {j} p = η .π _ j p
