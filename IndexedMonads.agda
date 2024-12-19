open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives using (Level; ℓ-zero; ℓ-suc)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep; funExtNonDep; funExtNonDep⁻)
open import Cubical.Foundations.Function using (idfun; curry; uncurry; _∘_)

open import Prelude

module IndexedMonads (I : Type) where

record IndexedContainer  : Type (ℓ-suc ℓ-zero) where
  field
    S : (i : I) → Type
    P : {i : I} → S i → (j : I) → Type

module _ where
  open IndexedContainer

  record _⇒_ (F G : IndexedContainer) : Type (ℓ-suc ℓ-zero) where
    field
      σ : ∀ {i} → F .S i → G .S i
      π : ∀ {i} (s : F .S i) {j} → G .P (σ s) j → F .P s j

  open _⇒_ public

  module _ {F G : IndexedContainer} {α β : F ⇒ G} where
    ⇒PathP :
      (≡σ : (λ {i} → α .σ {i}) ≡ β .σ)
      (≡π : PathP {ℓ-zero} (λ ι → ∀ {i} (s : F .S i) {j} → G .P (≡σ ι s) j → F .P s j) (λ {i} → α .π {i}) (β .π))
      → α ≡ β
    ⇒PathP ≡σ ≡π 𝒾 .σ = ≡σ 𝒾
    ⇒PathP ≡σ ≡π 𝒾 .π = ≡π 𝒾

    ⇒PathP-ext :
      (≡σ : ∀ {i} (s : F .S i) → α .σ s ≡ β .σ s)
      (≡π : ∀ (i : I) (s : F .S i) j
        → {p₁ : G .P (α .σ s) j} {p₂ : G .P (β .σ s) j}
          (p≡ : p₁ ≡[ ≡σ s , (λ s′ → G .P s′ j) ] p₂)
        → (α .π s p₁) ≡ (β .π s p₂))
      → α ≡ β
    ⇒PathP-ext ≡σ ≡π = ⇒PathP
      (implicitFunExt λ {i} → funExt ≡σ)
      (implicitFunExt λ {i} → funExt λ s → implicitFunExt λ {j} → funExtNonDep (≡π i s j))

    substDomain : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {x y : A}
      (B : A → Type ℓ′) {C : Type ℓ″}
      (x≡y : x ≡ y)
      (f : B y → C)
      → subst (λ a → B a → C) x≡y (subst B x≡y » f) ≡ f
    substDomain {A} {x} {y} B {C} =
      J
        (λ z x≡z → (f : B z → C) → subst (λ a → B a → C) x≡z (subst B x≡z » f) ≡ f)
        goal
      where module _ (f : B x → C) where
        B→C = λ a → B a → C

        aux : subst B refl » f ≡ f
        aux = funExt λ x → cong f (substRefl {B = B} x)

        goal : subst B→C refl (subst B refl » f) ≡ f 
        goal = substRefl {B = B→C} (subst B refl » f) ∙ aux

    ⇒PathP-ext″ :
      (≡σ : ∀ {i} (s : F .S i) → α .σ s ≡ β .σ s)
      (≡π : ∀ {i} (s : F .S i) {j} (p : G .P (β .σ s) j) → subst (λ s′ → G .P s′ j → F .P s j) (≡σ s) (α .π s) p ≡ β .π s p)
      → α ≡ β
    ⇒PathP-ext″ ≡σ ≡π = ⇒PathP
        (implicitFunExt λ {i} → funExt ≡σ)
        (implicitFunExt
          λ {i} → funExt
            λ s → implicitFunExt
              λ {j} → toPathP (funExt (≡π s))
        )

    ⇒PathP-ext′ :
      (≡σ : ∀ {i} (s : F .S i) → α .σ s ≡ β .σ s)
      (≡π : ∀ {i} (s : F .S i) {j} (p : G .P (α .σ s) j) → α .π s p ≡ β .π s (subst (λ s′ → G .P s′ j) (≡σ s) p))
      → α ≡ β
    ⇒PathP-ext′ ≡σ ≡π =
      ⇒PathP-ext″ ≡σ
        λ s {j} → funExt⁻ $
          let
            ≡π-ext⁻ : α .π s ≡ subst (λ s′ → P G s′ j) (≡σ s) » β .π s
            ≡π-ext⁻ = funExt $ ≡π s {j}
          in cong (subst (λ s′ → P G s′ j → P F s j) (≡σ s)) ≡π-ext⁻ ∙ substDomain (λ s′ → P G s′ j) (≡σ s) (β .π s {j})

    σ≡ : ∀ (α≡β : α ≡ β) {i} (s : F .S i) → α .σ s ≡ β .σ s
    σ≡ α≡β s = cong (λ γ → γ .σ s) α≡β

    π≡ : ∀ (α≡β : α ≡ β) {i} (s : F .S i) {j} (p : G .P _ j) → α .π s p ≡ β .π s (subst (λ s → G .P s j) (σ≡ α≡β s) p)
    π≡ α≡β s p = (funExtNonDep⁻ $ cong (λ γ → γ .π s) α≡β) (toPathP refl)
      where
      open import Cubical.Functions.FunExtEquiv using (funExtNonDep⁻)

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
    _⊗_ : IndexedContainer
    _⊗_ .S = ⟦ G ⟧ (F .S) 
    _⊗_ .P (s , v) k = Σ[ j ∈ I ] Σ[ p ∈ G .P s j ] F .P (v p) k

    -- interpretation is strong monoidal
    -- module _ (X : I → Type) (i : I) where
    --   ⊗-≃ : ∀ i → ⟦ G ⟧ (⟦ F ⟧ X) i ≃ ⟦ _⊗_ ⟧ X i
    --   ⊗-≃ i = isoToEquiv ⊗-iso where
    --     open Iso
    --     ⊗-iso : Iso (⟦ G ⟧ (⟦ F ⟧ X) i) (⟦ _⊗_ ⟧ X i)
    --     -- ⊗-iso .fun (s′ , br) = (s′ , λ j p → br j p .fst) , λ { k (j , (p′ , p)) → br j p′ .snd k p }
    --     ⊗-iso .fun (s′ , br) = {! !}
    --     -- ⊗-iso .inv ((s′ , br) , ⊗ops) = s′ , λ { j p′ → br j p′ , λ { k p → ⊗ops k (j , p′ , p) } }
    --     ⊗-iso .inv ((s′ , br) , ⊗ops) = {! !}
    --     ⊗-iso .rightInv _ = refl
    --     ⊗-iso .leftInv _ = refl

module _ {F G H K} where
  _⊗ₕ_ : (α : F ⇒ H) (β : G ⇒ K) → (F ⊗ G) ⇒ (H ⊗ K)
  (α ⊗ₕ β) .σ (Gs , Gsp→Fs) = β .σ Gs , λ { {j} Ksp → α .σ (Gsp→Fs (β .π Gs Ksp)) }
  (α ⊗ₕ β) .π {i} (Gs , Gsp→Fs) (i′ , Kp , Hp) = let
      Gsp = β .π Gs Kp 
    in i′ , Gsp , α .π (Gsp→Fs Gsp) Hp

module _ {F G H} where
  _⊗ᵥ_ : (α : F ⇒ G) (β : G ⇒ H) → (F ⇒ H)
  (α ⊗ᵥ β) .σ s = β .σ (α .σ s)
  (α ⊗ᵥ β) .π s p = α .π s (β .π (α .σ s) p)

-- module _ {F G} where
--   id₁-⊗ₕ : id₁ {F} ⊗ₕ id₁ {G} ≡ id₁ {F ⊗ G}
--   id₁-⊗ₕ = ⇒PathP-ext′
--     (λ { s → refl })
--     (λ { s p → sym $ substRefl p })
--
-- -- module _ {F G} (α : F ⇒ G) where
--   record ⇒Iso : Type ℓ-zero where
--     field
--       inv : G ⇒ F
--       inv-l : α ⊗ᵥ inv ≡ id₁
--       inv-r : inv ⊗ᵥ α ≡ id₁
--
module _ {F} where

  open IndexedContainer F

  -- open ⇒Iso

  unitor-l : (idᶜ ⊗ F) ⇒ F
  unitor-l .σ (s , _) = s
  unitor-l .π {i} (s , _) {j} p = j , p , refl

  -- unitor-l-inv : F ⇒ (idᶜ ⊗ F)
  -- unitor-l-inv .σ s = s , _
  -- unitor-l-inv .π s (k , p , k≡j) = subst (P s) k≡j p
  --
  -- unitor-l-iso : ⇒Iso unitor-l
  -- unitor-l-iso .inv = unitor-l-inv
  -- unitor-l-iso .inv-l = ⇒PathP-ext′
  --   (λ { s → refl })
  --   λ { s p → sym $ substRefl p }
  -- unitor-l-iso .inv-r = {! !}


  unitor-r : (F ⊗ idᶜ) ⇒ F
  unitor-r .σ (_ , si) = si refl
  unitor-r .π {i} (_ , si) p = i , refl , p

module _ {F G H} where
  associator : (F ⊗ (G ⊗ H)) ⇒ ((F ⊗ G) ⊗ H)
  associator .σ ((s″ , op″) , op′) = s″ , λ {j} p″ → op″ p″ , λ p′ → op′ (j , p″ , p′)
  associator .π ((s″ , op″) , op′) (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p

_² : IndexedContainer → IndexedContainer
IC ² = IC ⊗ IC

module _ (T : IndexedContainer) where 
  open IndexedContainer T

  ΣP : {i : I} → S i → Type
  ΣP s = Σ I (P s)

  record RawICMonoid : Type (ℓ-suc ℓ-zero) where
    field
      η : idᶜ ⇒ T
      μ : (T ²) ⇒ T

  record isICMonoid (raw : RawICMonoid) : Type (ℓ-suc ℓ-zero) where
    open RawICMonoid raw
    field
      η-unit-l : (η ⊗ₕ id₁) ⊗ᵥ μ ≡ unitor-l
      η-unit-r : (id₁ {F = T} ⊗ₕ η) ⊗ᵥ μ ≡ unitor-r
      μ-assoc : (id₁ {F = T} ⊗ₕ μ) ⊗ᵥ μ ≡ (associator {F = T} ⊗ᵥ ((μ ⊗ₕ id₁) ⊗ᵥ μ))

  record RawICMS : Type ℓ-zero where
    infixl 24 _•_
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

    infixl 24 _Π•_
    _Π•_ : ∀ {i} {s : S i}
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        → ∀ {j} (p : P s j) → S j
    (s′ Π• s″) {j} p = s′ p • s″ j p

    smoosh : ∀ {i} {s : S i}
        {s′ : {j : I} → P s j → S j}
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        → ∀ {j} (p : P (s • s′) j) → S j
    smoosh {s′} s″ p = s″ (s′ ↑ p) (s′ ↖ p) (s′ ↗ p)

    curry″ : ∀ {i} {s : S i}
        {s′ : {j : I} → P s j → S j}
        (s″ : {j : I} → Σ I (λ k → Σ (P s k) (λ p → P (s′ p) j)) → S j)
        → {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j
    curry″ s″ k p q = s″ (k , p , q)

  record isICMS (raw : RawICMS) : Type ℓ-zero where
    open RawICMS raw
    field
      e-unit-l : ∀ {i} (s : S i) → s • (λ {j} _ → e j) ≡ s 

      -- new
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

      -- new
      ↗-unit-l : ∀ {i} {s : S i} {j}
        → (p : P (s • (λ {j} _ → e j)) j)  
        → let
            tr = subst (_≡ j) (↑-unit-l p)
          in
            tr $ P-e-idx ((λ {j} _ → e j) ↗ p) ≡ refl

      e-unit-r : ∀ {i} (ss : ∀ {j} → i ≡ j → S j)
        → e i • (λ p → ss (P-e-idx p)) ≡ ss refl 

      -- new
      ↑-unit-r : ∀ {i} (ss : ∀ {j} → i ≡ j → S j) {j}
        → (p : P (e i • (λ p → ss (P-e-idx p))) j)
        → (λ p′ → ss (P-e-idx p′)) ↑ p ≡ i

      -- new
      ↖-unit-r : ∀ {i} (ss : ∀ {j} → i ≡ j → S j) {j}
        → (p : P (e i • (λ p → ss (P-e-idx p))) j)
        → let
            tr = subst (i ≡_) (↑-unit-r ss p)
          in
            tr $ P-e-idx ((λ p′ → ss (P-e-idx p′)) ↖ p) ≡ refl

      ↗-unit-r : ∀ {i} (ss : ∀ {j} → i ≡ j → S j) {j}
        → (p : P (e i • (λ p → ss (P-e-idx p))) j)
        → let
            -- What exactly is this?
            -- Looks like a subst (P _ j) (cong₂ something something) with
            -- an implicit first argument but I don't feel like refactoring it
            tr₁ = transport (λ ι → P (ss (toPathP {A = λ κ → i ≡ ↑-unit-r ss p κ} (↖-unit-r ss p) ι)) j)
            tr₂ = subst (λ s → P s j) (e-unit-r ss)
          in
            tr₁ $ (λ p′ → ss (P-e-idx p′)) ↗ p ≡ tr₂ p

      •-assoc : ∀ {i} 
        (s : S i)
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        → s • s′ • smoosh s″ ≡ s • (s′ Π• s″)

      -- new
      ↑-↗↑-assoc : ∀ {i} {j} 
        (s : S i)
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        (p : P (s • s′ • smoosh s″) j) 
        → let
          tr = subst (λ s → P s j) (•-assoc s s′ s″)
        in
            smoosh s″ ↑ p ≡ (s″ (s′ Π• s″ ↑ tr p) (s′ Π• s″ ↖ tr p )) ↑ (s′ Π• s″ ↗ tr p)

      -- new
      ↖↑-↑-assoc : ∀ {i} {j} 
        (s : S i)
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        (p : P (s • s′ •  smoosh s″) j) 
        → let
          tr = subst (λ s → P s j) (•-assoc s s′ s″)
        in
            s′ ↑ (smoosh s″ ↖ p) ≡ s′ Π• s″ ↑ tr p

      ↖↖-↖-assoc : ∀ {i} {j} 
        (s : S i)
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        (p : P (s • s′ • smoosh s″) j) 
        → let
          trl = subst (P s) (↖↑-↑-assoc s s′ s″ p) 
          trr = subst (λ s → P s j) (•-assoc s s′ s″)
        in
          trl $ s′ ↖ (smoosh s″ ↖ p) ≡ s′ Π• s″ ↖ trr p

      ↖↗-↗↖-assoc : ∀ {i} {j} 
        (s : S i)
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        (p : P (s • s′ • smoosh s″) j) 
        → let
          trl = transport
              (λ ι → P (s′ (toPathP {A = λ κ → P s (↖↑-↑-assoc s s′ s″ p κ)} (↖↖-↖-assoc s s′ s″ p) ι))
                 (↑-↗↑-assoc s s′ s″ p ι))
          trr = subst (λ s → P s j) (•-assoc s s′ s″)
        in trl $ s′ ↗ (smoosh s″ ↖ p)
          ≡ (s″ 
              (s′ Π• s″ ↑ trr p)
              (s′ Π• s″ ↖ trr p)
            ) ↖ (s′ Π• s″ ↗ trr p)                                     

      ↗-↗↗-assoc : ∀ {i} {j} 
        (s : S i)
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        (p : P (s • s′ • smoosh s″) j)
        → let
          trl = transport (λ ι →
            P
              {↑-↗↑-assoc s s′ s″ p ι}
              (s″
                (↖↑-↑-assoc s s′ s″ p ι)
                (toPathP {A = λ κ → P s (↖↑-↑-assoc s s′ s″ p κ)} (↖↖-↖-assoc s s′ s″ p) ι)
                (toPathP
                  {A = λ κ → P (s′ $ toPathP {A = λ κ → P s (↖↑-↑-assoc s s′ s″ p κ)} (↖↖-↖-assoc s s′ s″ p) κ) (↑-↗↑-assoc s s′ s″ p κ)}
                  (↖↗-↗↖-assoc s s′ s″ p)
                  ι
                )
              )
              j
            )
          trr = subst (λ s → P s j) (•-assoc s s′ s″)
            in
               trl $ smoosh s″ ↗ p
            ≡
              s″ ((s′ Π• s″) ↑ trr p) ((s′ Π• s″) ↖ trr p) ↗ ((s′ Π• s″) ↗ trr p)

  record ICMS : Type ℓ-zero where
    field
      icms : RawICMS
      is-icms : isICMS icms

  module _ (icms : RawICMS) where
    open RawICMS icms
    open RawICMonoid

    RawICMS→RawICMonoid : RawICMonoid
    RawICMS→RawICMonoid .η .σ {i} _ = e i
    RawICMS→RawICMonoid .η .π _ p = P-e-idx p
    RawICMS→RawICMonoid .μ .σ (s , v) = s • v
    RawICMS→RawICMonoid .μ .π (s , v) p = v ↑ p , v ↖ p , v ↗ p

    open isICMonoid

    module _ (is-icms : isICMS icms) where
      open isICMS is-icms

      isICMS→isICMonoid : isICMonoid RawICMS→RawICMonoid
      isICMS→isICMonoid .η-unit-l = ⇒PathP-ext′
        (λ { (s , v) → e-unit-l s })
        λ { (s , v) p → ΣPathP
          ( ↑-unit-l p
          , ΣPathP 
            ( toPathP (↖-unit-l p)
            , toPathP (↗-unit-l p)
            )
          )
        }
      isICMS→isICMonoid .η-unit-r = ⇒PathP-ext′
        (λ { (_ , ss) → e-unit-r ss })
        λ { (_ , ss) p → ΣPathP
          ( ↑-unit-r ss p
          , ΣPathP
            ( toPathP (↖-unit-r ss p)
            , toPathP (↗-unit-r ss p)
            )
          )
        }
      isICMS→isICMonoid .μ-assoc = ⇒PathP-ext′
        (λ { ((s , s′) , s″) → •-assoc s s′ (curry″ s″) })
        λ { ((s , s′) , s″) p → ΣPathP
          ( ↑-↗↑-assoc s s′ (curry″ s″) p 
          , ΣPathP
            ( ΣPathP
              ( ↖↑-↑-assoc s s′ (curry″ s″) p
              , ΣPathP
                ( toPathP (↖↖-↖-assoc s s′ (curry″ s″) p)
                , toPathP (↖↗-↗↖-assoc s s′ (curry″ s″) p)
                )
              )
            , toPathP (↗-↗↗-assoc s s′ (curry″ s″) p)
            )
          )
        }

  module _ (icmon : RawICMonoid) where
    open RawICMS
    open RawICMonoid icmon

    RawICMonoid→RawICMS : RawICMS
    RawICMonoid→RawICMS .e i = η .σ _
    RawICMonoid→RawICMS ._•_ s v = μ .σ (s , v)
    RawICMonoid→RawICMS ._↑_ {s} v p = μ .π (s , v) p .fst
    RawICMonoid→RawICMS ._↖_ {s} v p = μ .π (s , v) p .snd .fst
    RawICMonoid→RawICMS ._↗_ {s} v p = μ .π (s , v) p .snd .snd
    RawICMonoid→RawICMS .P-e-idx p = η .π _ p

    module _ (is-icmon : isICMonoid icmon) where
      open isICMS
      open isICMonoid is-icmon

      isICMonoid→isICMS : isICMS RawICMonoid→RawICMS
      isICMonoid→isICMS .e-unit-l s = σ≡ η-unit-l (s , _)
      isICMonoid→isICMS .↑-unit-l {s} p = 
        let
          Σeq = π≡ η-unit-l (s , _) p
        in cong fst Σeq
      isICMonoid→isICMS .↖-unit-l {s} p =
        let
          Σeq = π≡ η-unit-l (s , _) p
        in fromPathP $ cong (snd » fst) Σeq
      isICMonoid→isICMS .↗-unit-l {s} p =
        let
          Σeq = π≡ η-unit-l (s , _) p
        in fromPathP $ cong (snd » snd) Σeq
      isICMonoid→isICMS .e-unit-r {i} ss = σ≡ η-unit-r (_ , ss)
      isICMonoid→isICMS .↑-unit-r ss p =
        let
          Σeq = π≡ η-unit-r (_ , ss) p
        in cong fst Σeq
      isICMonoid→isICMS .↖-unit-r ss p = 
        let
          Σeq = π≡ η-unit-r (_ , ss) p
        in fromPathP $ cong (snd » fst) Σeq
      isICMonoid→isICMS .↗-unit-r {i = i} ss {j = j} p = 
        let
          Σeq = π≡ η-unit-r (_ , ss) p
          xx = cong (snd » snd) Σeq
        in idfun
          ( transport (λ ι → P (ss (toPathP {A = λ κ → i ≡ isICMonoid→isICMS .↑-unit-r ss p κ} (isICMonoid→isICMS .↖-unit-r ss p) ι)) j)
              $ RawICMonoid→RawICMS ._↗_ (λ p′ → ss (RawICMonoid→RawICMS .P-e-idx p′)) p
            ≡ subst (λ s → P s j) (isICMonoid→isICMS .e-unit-r ss) p
          )
          (fromPathP {A = λ ι → P (ss (toPathP {A = λ κ → i ≡ isICMonoid→isICMS .↑-unit-r ss p κ} (isICMonoid→isICMS .↖-unit-r ss p) ι)) j}
            {! xx !})
        where open import Cubical.Foundations.Path using (fromPathP⁻)
        -- ————————————————————————————————————————————————————————————
        -- Goal: PathP
        -- (λ ι →
        --    P
        --    (ss
        --     (toPathP
        --      (fromPathP $
        --       (λ i₁ →
        --          ((λ r → snd r) » (λ r → fst r)) (π≡ η-unit-r (tt , ss) p i₁)))
        --      ι))
        --    j)
        -- (μ .π (η .σ tt , (λ p′ → ss (η .π tt p′))) p .snd .snd)
        -- (subst (λ s → P s j) (σ≡ η-unit-r (tt , ss)) p)
        -- ————————————————————————————————————————————————————————————
        -- Have: PathP
        -- (λ ɩ →
        --  P (ss (
        --    ((funExtNonDep⁻ $ (λ κ → η-unit-r κ .π (tt , ss)))
        --     (toPathP refl)
        --     ɩ)
        --    .snd .fst))
        --  j)
        --   (μ .π (η .σ tt , (λ Ksp → id₁ .σ (ss (η .π tt Ksp)) )) p)
        --   (subst (λ s → P s j) (λ ɩ → η-unit-r ɩ .σ (tt , ss)) p)
        -- ————————————————————————————————————————————————————————————

      -- isICMonoid→isICMS .•-assoc = {! !}
      -- isICMonoid→isICMS .↑-↗↑-assoc = {! !}
      -- isICMonoid→isICMS .↖↑-↑-assoc = {! !}
      -- isICMonoid→isICMS .↖↖-↖-assoc = {! !}
      -- isICMonoid→isICMS .↖↗-↗↖-assoc = {! !}
      -- isICMonoid→isICMS .↗-↗↗-assoc = {! !}
      --
