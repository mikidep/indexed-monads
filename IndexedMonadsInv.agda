open import Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function using (idfun; curry; uncurry; _∘_)

module IndexedMonadsInv (I : Type) where

open import IndexedContainerSigma I

module _
  (T : IndexedContainer)
  (isSetS : ∀ {i} → isSet (T .IndexedContainer.S i))
  (isSetP : ∀ {i} {s : T .IndexedContainer.S i} {j} → isSet (T .IndexedContainer.P s j))
  where 

  open IndexedContainer T

  record RawICMonoid : Type (ℓ-suc ℓ-zero) where
    field
      η : idᶜ ⇒ T
      μ : (T ²) ⇒ T

  record isICMonoid (raw : RawICMonoid) : Type (ℓ-suc ℓ-zero) where
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
    const-e {_} {_} {j} _ = e j

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
      e-unit-l : ∀ {i} (s : S i)
        → s • (λ {j} _ → e j) ≡ s 

      ↖-unit-l : ∀ {i} (s : S i) {j} (p : P (s • const-e) j)
        → let
            trl = subst (P s) (P-e-idx (const-e ↗ p))
            trr = substP T (e-unit-l s) 
          in trl $ const-e ↖ p ≡ trr $ p

      e-unit-r : ∀ {i} (s : S i)
        → e i • (λ p → subst S (P-e-idx p) s) ≡ s
  --     -- new
  --     ↑-unit-l : ∀ {i} {s : S i} {j}
  --       → (p : P (s • (λ {j} _ → e j)) j)  
  --       → (λ {j} _ → e j) ↑ p ≡ j
  --
  --     ↖-unit-l : ∀ {i} {s : S i} {j}
  --       → (p : P (s • (λ {j} _ → e j)) j)  
  --       → let
  --           tr₁ = subst (P s) (↑-unit-l p)
  --           tr₂ = substP T (e-unit-l s)
  --         in
  --           tr₁ $ (λ {j} _ → e j) ↖ p ≡ tr₂ $ p
  --
  --     -- new
  --     ↗-unit-l : ∀ {i} {s : S i} {j}
  --       → (p : P (s • (λ {j} _ → e j)) j)  
  --       → let
  --           tr = subst (_≡ j) (↑-unit-l p)
  --         in
  --           tr $ P-e-idx ((λ {j} _ → e j) ↗ p) ≡ refl
  --
  --     e-unit-r : ∀ {i} (ss : ∀ {j} → i ≡ j → S j)
  --       → e i • (λ p → ss (P-e-idx p)) ≡ ss refl 
  --
  --     -- new
  --     ↑-unit-r : ∀ {i} (ss : ∀ {j} → i ≡ j → S j) {j}
  --       → (p : P (e i • (λ p → ss (P-e-idx p))) j)
  --       → (λ p′ → ss (P-e-idx p′)) ↑ p ≡ i
  --
  --     -- new
  --     ↖-unit-r : ∀ {i} (ss : ∀ {j} → i ≡ j → S j) {j}
  --       → (p : P (e i • (λ p → ss (P-e-idx p))) j)
  --       → let
  --           tr = subst (i ≡_) (↑-unit-r ss p)
  --         in
  --           tr $ P-e-idx ((λ p′ → ss (P-e-idx p′)) ↖ p) ≡ refl
  --
  --     ↗-unit-r : ∀ {i} (ss : ∀ {j} → i ≡ j → S j) {j}
  --       → (p : P (e i • (λ p → ss (P-e-idx p))) j)
  --       → let
  --           -- What exactly is this?
  --           -- Looks like a subst (P _ j) (cong₂ something something) with
  --           -- an implicit first argument but I don't feel like refactoring it
  --           tr₁ = transport (λ ι → P (ss (toPathP {A = λ κ → i ≡ ↑-unit-r ss p κ} (↖-unit-r ss p) ι)) j)
  --           tr₂ = substP T (e-unit-r ss)
  --         in
  --           tr₁ $ (λ p′ → ss (P-e-idx p′)) ↗ p ≡ tr₂ p
  --
  --     •-assoc : ∀ {i} 
  --       (s : S i)
  --       (s′ : {j : I} → P s j → S j)
  --       (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
  --       → s • s′ • smoosh s″ ≡ s • (s′ Π• s″)
  --
  --     -- new
  --     ↑-↗↑-assoc : ∀ {i} {j} 
  --       (s : S i)
  --       (s′ : {j : I} → P s j → S j)
  --       (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
  --       (p : P (s • s′ • smoosh s″) j) 
  --       → let
  --         tr = substP T (•-assoc s s′ s″)
  --       in
  --           smoosh s″ ↑ p ≡ (s″ (s′ Π• s″ ↑ tr p) (s′ Π• s″ ↖ tr p )) ↑ (s′ Π• s″ ↗ tr p)
  --
  --     -- new
  --     ↖↑-↑-assoc : ∀ {i} {j} 
  --       (s : S i)
  --       (s′ : {j : I} → P s j → S j)
  --       (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
  --       (p : P (s • s′ •  smoosh s″) j) 
  --       → let
  --         tr = substP T (•-assoc s s′ s″)
  --       in
  --           s′ ↑ (smoosh s″ ↖ p) ≡ s′ Π• s″ ↑ tr p
  --
  --     ↖↖-↖-assoc : ∀ {i} {j} 
  --       (s : S i)
  --       (s′ : {j : I} → P s j → S j)
  --       (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
  --       (p : P (s • s′ • smoosh s″) j) 
  --       → let
  --         trl = subst (P s) (↖↑-↑-assoc s s′ s″ p) 
  --         trr = substP T (•-assoc s s′ s″)
  --       in
  --         trl $ s′ ↖ (smoosh s″ ↖ p) ≡ s′ Π• s″ ↖ trr p
  --
  --     ↖↗-↗↖-assoc : ∀ {i} {j} 
  --       (s : S i)
  --       (s′ : {j : I} → P s j → S j)
  --       (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
  --       (p : P (s • s′ • smoosh s″) j) 
  --       → let
  --         trl = transport
  --             (λ ι → P (s′ (toPathP {A = λ κ → P s (↖↑-↑-assoc s s′ s″ p κ)} (↖↖-↖-assoc s s′ s″ p) ι))
  --                (↑-↗↑-assoc s s′ s″ p ι))
  --         trr = substP T (•-assoc s s′ s″)
  --       in trl $ s′ ↗ (smoosh s″ ↖ p)
  --         ≡ (s″ 
  --             (s′ Π• s″ ↑ trr p)
  --             (s′ Π• s″ ↖ trr p)
  --           ) ↖ (s′ Π• s″ ↗ trr p)                                     
  --
  --     ↗-↗↗-assoc : ∀ {i} {j} 
  --       (s : S i)
  --       (s′ : {j : I} → P s j → S j)
  --       (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
  --       (p : P (s • s′ • smoosh s″) j)
  --       → let
  --         trl = transport (λ ι →
  --           P
  --             {↑-↗↑-assoc s s′ s″ p ι}
  --             (s″
  --               (↖↑-↑-assoc s s′ s″ p ι)
  --               (toPathP {A = λ κ → P s (↖↑-↑-assoc s s′ s″ p κ)} (↖↖-↖-assoc s s′ s″ p) ι)
  --               (toPathP
  --                 {A = λ κ → P (s′ $ toPathP {A = λ κ → P s (↖↑-↑-assoc s s′ s″ p κ)} (↖↖-↖-assoc s s′ s″ p) κ) (↑-↗↑-assoc s s′ s″ p κ)}
  --                 (↖↗-↗↖-assoc s s′ s″ p)
  --                 ι
  --               )
  --             )
  --             j
  --           )
  --         trr = substP T (•-assoc s s′ s″)
  --           in
  --              trl $ smoosh s″ ↗ p
  --           ≡
  --             s″ ((s′ Π• s″) ↑ trr p) ((s′ Π• s″) ↖ trr p) ↗ ((s′ Π• s″) ↗ trr p)

  record ICMS : Type ℓ-zero where
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
      open import Cubical.Functions.FunExtEquiv using (funExtDep; heteroHomotopy≃Homotopy)
      open import Cubical.Foundations.Equiv using (invEq)
      open isICMS is-icms

      isICMS→isICMonoid : isICMonoid RawICMS→RawICMonoid
      isICMS→isICMonoid .η-unit-l = ⇒PathP λ s → Π⇒PathP
        (e-unit-l s)
        (implicitFunExt λ {j} →
          funExtNonDepHet (↖-unit-l s) 
        )
      isICMS→isICMonoid .η-unit-r = ⇒PathP λ s → Π⇒PathP
        (e-unit-r s)
        (implicitFunExt λ {j} →
          funExtNonDepHet {! !} 
        )
      isICMS→isICMonoid .μ-assoc = {! !}
  --     isICMS→isICMonoid .η-unit-l = ⇒PathP-ext′
  --       (λ { (s , v) → e-unit-l s })
  --       λ { (s , v) p → ΣPathP
  --         ( ↑-unit-l p
  --         , ΣPathP 
  --           ( toPathP (↖-unit-l p)
  --           , toPathP (↗-unit-l p)
  --           )
  --         )
  --       }
  --     isICMS→isICMonoid .η-unit-r = ⇒PathP-ext′
  --       (λ { (_ , ss) → e-unit-r ss })
  --       λ { (_ , ss) p → ΣPathP
  --         ( ↑-unit-r ss p
  --         , ΣPathP
  --           ( toPathP (↖-unit-r ss p)
  --           , toPathP (↗-unit-r ss p)
  --           )
  --         )
  --       }
  --     isICMS→isICMonoid .μ-assoc = ⇒PathP-ext′
  --       (λ { ((s , s′) , s″) → •-assoc s s′ (curry″ s″) })
  --       λ { ((s , s′) , s″) p → ΣPathP
  --         ( ↑-↗↑-assoc s s′ (curry″ s″) p 
  --         , ΣPathP
  --           ( ΣPathP
  --             ( ↖↑-↑-assoc s s′ (curry″ s″) p
  --             , ΣPathP
  --               ( toPathP (↖↖-↖-assoc s s′ (curry″ s″) p)
  --               , toPathP (↖↗-↗↖-assoc s s′ (curry″ s″) p)
  --               )
  --             )
  --           , toPathP (↗-↗↗-assoc s s′ (curry″ s″) p)
  --           )
  --         )
  --       }
  --
  -- module _ (icmon : RawICMonoid) where
  --   open RawICMS
  --   open RawICMonoid icmon
  --
  --   RawICMonoid→RawICMS : RawICMS
  --   RawICMonoid→RawICMS .e i = η .σ _
  --   RawICMonoid→RawICMS ._•_ s v = μ .σ (s , v)
  --   RawICMonoid→RawICMS ._↑_ {s} v p = μ .π (s , v) p .fst
  --   RawICMonoid→RawICMS ._↖_ {s} v p = μ .π (s , v) p .snd .fst
  --   RawICMonoid→RawICMS ._↗_ {s} v p = μ .π (s , v) p .snd .snd
  --   RawICMonoid→RawICMS .P-e-idx p = η .π _ p
  --
  --   module _ (is-icmon : isICMonoid icmon) where
  --     open isICMS
  --     open isICMonoid is-icmon
  --
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
  --
  --     -- isICMonoid→isICMS .•-assoc = {! !}
  --     -- isICMonoid→isICMS .↑-↗↑-assoc = {! !}
  --     -- isICMonoid→isICMS .↖↑-↑-assoc = {! !}
  --     -- isICMonoid→isICMS .↖↖-↖-assoc = {! !}
  --     -- isICMonoid→isICMS .↖↗-↗↖-assoc = {! !}
  --     -- isICMonoid→isICMS .↗-↗↗-assoc = {! !}
  --     --
