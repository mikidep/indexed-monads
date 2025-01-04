open import Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function using (idfun; curry; uncurry; _∘_)

module IndexedMonads (I : Type) where

open import IndexedContainer I

module _
  (T : IndexedContainer)
  (isSetS : ∀ {i} → isSet (T .IndexedContainer.S i))
  (isSetP : ∀ {i} {s : T .IndexedContainer.S i} {j} → isSet (T .IndexedContainer.P s j))
  where 

  open IndexedContainer T

  record RawICMonoid : Type where
    field
      η : idᶜ ⇒ T
      μ : (T ²) ⇒ T

  record isICMonoid (raw : RawICMonoid) : Type where
    open RawICMonoid raw
    field
      η-unit-l : unitor-l-inv ; (η ⊗₁ id₁ T) ; μ ≡ id₁ T
      η-unit-r : unitor-r-inv ; (id₁ T ⊗₁ η) ; μ ≡ id₁ T
      μ-assoc : (id₁ T ⊗₁ μ) ; μ ≡ (associator {F = T} ; ((μ ⊗₁ id₁ T) ; μ))

  record RawICMS : Type where
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

    const-e : ∀ {i : I} {s : S i} {j : I} (p : P s j) → S j
    const-e {j} _ = e j

    substS-Pe : ∀ {i : I} (s : S i) {k : I} → P (e i) k → S k
    substS-Pe s p = subst S (P-e-idx p) s

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

  record isICMS (raw : RawICMS) : Type where
    open RawICMS raw
    field
      e-unit-l : ∀ {i} (s : S i)
        → s • const-e ≡ s 

      ↖-unit-l : ∀ {i} (s : S i) {j}
        → PathP (λ z → P (e-unit-l s z) j → P s j)
          (λ (p : P (s • const-e) j) →
             (subst (P s) (P-e-idx (const-e ↗ p)))
             (const-e ↖ p)
          )
          (λ p → p)

      e-unit-r : ∀ {i} (s : S i)
        → e i • (λ p → subst S (P-e-idx p) s) ≡ s

      ↗-unit-r : ∀ {i} (s : S i) {j}
        → PathP (λ ι → P (e-unit-r s ι) j → P s j)
          (λ p →
            let eq = P-e-idx (substS-Pe s ↖ p) 
            in transport
              (cong₂ (λ i s → P {i} s j) (sym eq) (symP $ subst-filler S eq s))
              (substS-Pe s ↗ p)
          )
          (λ p → p)

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
        → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → I) 
          (λ p → smoosh s″ ↑ p)
          (λ p → s″ ((s′ Π• s″) ↑ p) ((s′ Π• s″) ↖ p) ↑ (s′ Π• s″ ↗ p)) 

      -- new
      ↖↑-↑-assoc : ∀ {i} {j} 
        (s : S i)
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → I) 
            (λ p → s′ ↑ (smoosh s″ ↖ p))
            (λ p → (s′ Π• s″) ↑ p)

      ↖↖-↖-assoc : ∀ {i} {j} 
        (s : S i)
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P s (↖↑-↑-assoc s s′ s″ ι p)) 
          (λ p → s′ ↖ (smoosh s″ ↖ p))
          (λ p → s′ Π• s″ ↖ p)

      ↖↗-↗↖-assoc : ∀ {i} {j} 
        (s : S i)
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P (s′ (↖↖-↖-assoc s s′ s″ ι p)) (↑-↗↑-assoc s s′ s″ ι p)) 
          (λ p → s′ ↗ (smoosh s″ ↖ p))
          (λ p → s″ (s′ Π• s″ ↑ p) (s′ Π• s″ ↖ p) ↖ (s′ Π• s″ ↗ p)) 

      ↗-↗↗-assoc : ∀ {i} {j} 
        (s : S i)
        (s′ : {j : I} → P s j → S j)
        (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
        → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P (s″ (↖↑-↑-assoc s s′ s″ ι p) (↖↖-↖-assoc s s′ s″ ι p) (↖↗-↗↖-assoc s s′ s″ ι p)) j)
          (λ p → smoosh s″ ↗ p)
          (λ p → s″ ((s′ Π• s″) ↑ p) ((s′ Π• s″) ↖ p) ↗ ((s′ Π• s″) ↗ p))

  record ICMS : Type where
    field
      icms : RawICMS
      is-icms : isICMS icms

  module _ (icms : RawICMS) where
    open RawICMS icms
    open RawICMonoid

    RawICMS→RawICMonoid : RawICMonoid
    RawICMS→RawICMonoid .η i _ .σs = e i
    RawICMS→RawICMonoid .η _ _ .πs p = P-e-idx p
    RawICMS→RawICMonoid .μ _ (s , v) .σs = s • v
    RawICMS→RawICMonoid .μ _ (_ , v) .πs p = v ↑ p , v ↖ p , v ↗ p

    open isICMonoid

    module _ (is-icms : isICMS icms) where
      open import Cubical.Functions.FunExtEquiv using (funExtDep; funExtNonDep; heteroHomotopy≃Homotopy)
      open import Cubical.Foundations.Equiv using (invEq)
      open isICMS is-icms

      isICMS→isICMonoid : isICMonoid RawICMS→RawICMonoid
      isICMS→isICMonoid .η-unit-l = ⇒PathP λ s → Π⇒PathP
        (e-unit-l s)
        (implicitFunExt λ {j} → ↖-unit-l s)
      isICMS→isICMonoid .η-unit-r = ⇒PathP λ {i} s → Π⇒PathP
        (e-unit-r s)
        (implicitFunExt λ {j} → ↗-unit-r s)
      isICMS→isICMonoid .μ-assoc = ⇒PathP λ { ((s , s′) , s″) → Π⇒PathP
          (•-assoc s s′ (curry″ s″))
          (implicitFunExt λ {j} →
            λ { ι p →
                ↑-↗↑-assoc s s′ (curry″ s″) ι p 
              , ( ↖↑-↑-assoc s s′ (curry″ s″) ι p 
                , ↖↖-↖-assoc s s′ (curry″ s″) ι p 
                , ↖↗-↗↖-assoc s s′ (curry″ s″) ι p
                ) 
              , ↗-↗↗-assoc s s′ (curry″ s″) ι p
            }
          )
        }

  module _ (icmon : RawICMonoid) where
    open RawICMS
    open RawICMonoid icmon

    RawICMonoid→RawICMS : RawICMS
    RawICMonoid→RawICMS .e i = η i _ .σs
    RawICMonoid→RawICMS .P-e-idx {i} p = η i _ .πs p
    RawICMonoid→RawICMS ._•_ {i} s v = μ i (s , v) .σs
    RawICMonoid→RawICMS ._↑_ {i} {s} v p = μ i (s , v) .πs p .fst
    RawICMonoid→RawICMS ._↖_ {i} {s} v p = μ i (s , v) .πs p .snd .fst
    RawICMonoid→RawICMS ._↗_ {i} {s} v p = μ i (s , v) .πs p .snd .snd

    module _ (is-icmon : isICMonoid icmon) where
      open import Cubical.Functions.FunExtEquiv using (funExtDep⁻)

      open isICMS
      open isICMonoid is-icmon

      isICMonoid→isICMS : isICMS RawICMonoid→RawICMS
      isICMonoid→isICMS .e-unit-l = σs≡ η-unit-l 
      isICMonoid→isICMS .↖-unit-l = πs≡ η-unit-l
      isICMonoid→isICMS .e-unit-r = σs≡ η-unit-r
      isICMonoid→isICMS .↗-unit-r = πs≡ η-unit-r
      isICMonoid→isICMS .•-assoc = {! !}
      isICMonoid→isICMS .↑-↗↑-assoc = {! !}
      isICMonoid→isICMS .↖↑-↑-assoc = {! !}
      isICMonoid→isICMS .↖↖-↖-assoc = {! !}
      isICMonoid→isICMS .↖↗-↗↖-assoc = {! !}
      isICMonoid→isICMS .↗-↗↗-assoc = {! !}

  --     isICMonoid→isICMS : isICMS RawICMonoid→RawICMS
  --     isICMonoid→isICMS .e-unit-l s = σ≡ η-unit-l (s , _)
  --     isICMonoid→isICMS .↑-unit-l {s} p = 
  --       let
  --         Σeq = π≡ η-unit-l (s , _) p
  --       in cong fst Σeq
  --     isICMonoid→isICMS .↖-unit-l {s} p =
  --       let
  --         Σeq = π≡ η-unit-l (s , _) p
  --       in fromPathP $ cong (snd » fst) Σeq
  --     isICMonoid→isICMS .↗-unit-l {s} p =
  --       let
  --         Σeq = π≡ η-unit-l (s , _) p
  --       in fromPathP $ cong (snd » snd) Σeq
  --     isICMonoid→isICMS .e-unit-r {i} ss = σ≡ η-unit-r (_ , ss)
  --     isICMonoid→isICMS .↑-unit-r ss p =
  --       let
  --         Σeq = π≡ η-unit-r (_ , ss) p
  --       in cong fst Σeq
  --     isICMonoid→isICMS .↖-unit-r ss p = 
  --       let
  --         Σeq = π≡ η-unit-r (_ , ss) p
  --       in fromPathP $ cong (snd » fst) Σeq
  --     isICMonoid→isICMS .↗-unit-r {i = i} ss {j = j} p = 
  --       let
  --         Σeq = π≡ η-unit-r (_ , ss) p
  --         xx = cong (snd » snd) Σeq
  --         retraction : toPathP (fromPathP (λ κ → π≡ η-unit-r (tt , ss) p κ .snd .fst)) ≡ (λ κ → π≡ η-unit-r (tt , ss) p κ .snd .fst)
  --         retraction = PathPIsoPath (λ κ → i ≡ cong fst Σeq κ) _ _ .Iso.leftInv (λ κ → π≡ η-unit-r (tt , ss) p κ .snd .fst)
  --         -- tr = subst
  --         --     ( λ x → transport
  --         --         (λ ι → P (ss x) j) ?
  --         --       ≡ ?
  --         --     ) (sym retraction)
  --       in idfun
  --         ( transport
  --             (λ ι → P (ss (toPathP {A = λ κ → i ≡ cong fst Σeq κ} (fromPathP (λ κ → π≡ η-unit-r (tt , ss) p κ .snd .fst)) ι)) j) $
  --               μ .π (η .σ tt , (λ p′ → ss (η .π tt p′))) p .snd .snd
  --           ≡ substP T (σ≡ η-unit-r (tt , ss)) p
  --         )
  --         {! PathPIsoPath (λ κ → i ≡ cong fst Σeq κ) _ _ .Iso.leftInv !}
  --       where
  --         open import Cubical.Foundations.Path
  --         open import Cubical.Foundations.Isomorphism
  --       -- ————————————————————————————————————————————————————————————
  --       -- Goal: PathP
  --       -- (λ ι → P (ss
  --       --     (toPathP
  --       --      (fromPathP $
  --       --       (λ i₁ →
  --       --          ((λ r → snd r) » (λ r → fst r)) (π≡ η-unit-r (tt , ss) p i₁)))
  --       --      ι))
  --       --    j)
  --       -- (μ .π (η .σ tt , (λ p′ → ss (η .π tt p′))) p .snd .snd)
  --       -- (substP T (σ≡ η-unit-r (tt , ss)) p)
  --       -- ————————————————————————————————————————————————————————————
  --       -- Have: PathP
  --       -- (λ ɩ → P (ss (
  --       --    ((funExtNonDep⁻ $ (λ κ → η-unit-r κ .π (tt , ss)))
  --       --     (toPathP refl)
  --       --     ɩ)
  --       --    .snd .fst))
  --       --  j)
  --       --   (μ .π (η .σ tt , (λ Ksp → id₁ .σ (ss (η .π tt Ksp)) )) p)
  --       --   (substP T (λ ɩ → η-unit-r ɩ .σ (tt , ss)) p)
  --       -- ————————————————————————————————————————————————————————————
