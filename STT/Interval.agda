{-# OPTIONS --cubical --guardedness --lossy-unification #-}

{-
This file contains a definition of orthogonality and proof of various
closure properties
-}

module STT.Interval where

-- Local imports
open import Prelude
open import Categories.ProtoWildCat
open import Categories.Map
open import LeibnizConstruction.Map
open import LeibnizConstruction.Orthogonality

-- Library imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat.Order.Inductive

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Nat hiding (_!) renaming (elim to elimℕ)
open import Cubical.Data.Fin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty renaming (⊥ to ∅)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.Pushout


open Iso

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Type ℓ₁
    B : Type ℓ₂
    X : Type ℓ₃
    Y : Type ℓ₄

PathFin : {n m : ℕ} {p q : n <ᵗ m} → Path (Fin m) (n , p) (n , q)
PathFin = Σ≡Prop (λ _ → isProp<ᵗ) refl

open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.CommMonoid

record IsBoundedDistLattice {L : Type ℓ} (0l 1l : L)
  (_∨l_ _∧l_ : L → L → L)  : Type ℓ where
  constructor isboundeddistlattice
  field
    isDistLattice : IsDistLattice 0l 1l _∨l_ _∧l_
    ∧l-1l : (x : L) → x ∧l 1l ≡ x
    ∨l-1l : (x : L) → x ∨l 1l ≡ 1l
    ∨l-0l : (x : L) → x ∨l 0l ≡ x
    ∧l-0l : (x : L) → x ∧l 0l ≡ 0l

  open IsDistLattice isDistLattice

  1l-∧l : (x : L) → 1l ∧l x ≡ x
  1l-∧l x = ∧lComm _ _ ∙ ∧l-1l x

  0l-∨l : (x : L) → 0l ∨l x ≡ x
  0l-∨l x = ∨lComm _ _ ∙ ∨l-0l x

  1l-∨l : (x : L) → 1l ∨l x ≡ 1l
  1l-∨l x = ∨lComm _ _ ∙ ∨l-1l _

  0l-∧l : (x : L) → 0l ∧l x ≡ 0l
  0l-∧l x = ∧lComm _ _ ∙ ∧l-0l _

  idem∧ : (x : L) → x ∧l x ≡ x
  idem∧ x = cong₂ _∧l_ refl (sym (∨l-0l x)) ∙ absorb x 0l .snd

  idem∨ : (x : L) → x ∨l x ≡ x
  idem∨ x = cong₂ _∨l_ refl (sym (∧l-1l x)) ∙ absorb x 1l .fst

record BoundedDistLatticeStr (L : Type ℓ) : Type ℓ where
  field
    0l 1l : L
    _∨l_ _∧l_ : L → L → L
    isBoundedDistLattice : IsBoundedDistLattice 0l 1l _∨l_ _∧l_
    is-set : isSet L

Interval : (ℓ : Level) → Type (ℓ-suc ℓ)
Interval ℓ = Σ[ I ∈ Type ℓ ] BoundedDistLatticeStr I

module HornLifting (I' : Interval ℓ) where
  private
    𝐈 : Type ℓ
    𝐈 = fst I'
    BDLstr : BoundedDistLatticeStr 𝐈
    BDLstr = snd I'

  open BoundedDistLatticeStr BDLstr renaming (is-set to isSetI)
  open IsBoundedDistLattice isBoundedDistLattice
  open IsDistLattice isDistLattice
  module meet = IsSemilattice (IsLattice.meetSemilattice isLattice)
  module join = IsSemilattice (IsLattice.joinSemilattice isLattice)
  meetLattice : Semilattice _
  meetLattice .fst = _
  meetLattice .snd .SemilatticeStr.ε = _
  meetLattice .snd .SemilatticeStr._·_ = _
  meetLattice .snd .SemilatticeStr.isSemilattice =
     IsLattice.meetSemilattice isLattice

  _≤'_ : 𝐈 → 𝐈 → Type ℓ
  _≤'_ = MeetSemilattice._≤_
          (𝐈 , semilatticestr _ _ (IsLattice.meetSemilattice isLattice))

  hasΔStr : {n : ℕ} (x : Fin (2 + n) → 𝐈) → Type _
  hasΔStr {n = n} x = (x fzero ≡ 1l) × (x flast ≡ 0l)
             × ((i : Fin (suc n)) →  x (fsuc i) ≤' x (injectSuc i))

  Δ : (n : ℕ) → Type ℓ
  Δ n = Σ[ x ∈ (Fin (2 + n) → 𝐈) ] (hasΔStr x)

  isProp-hasΔStr : {n : ℕ} (x : Fin (2 + n) → 𝐈) → isProp (hasΔStr x)
  isProp-hasΔStr x =
    isPropΣ (is-set _ _)
       λ _ → isPropΣ (is-set _ _) λ _ → isPropΠ λ _ → is-set _ _

  isSetΔ : {n : ℕ} → isSet (Δ n)
  isSetΔ {n = n} =
    isSetΣ (isSetΠ (λ _ → is-set)) (λ f → isProp→isSet (isProp-hasΔStr f))

  open import Cubical.Relation.Binary.Order.Poset.Base

  decreasingΔ' : {n : ℕ} (x : Δ n) (b a : Fin (suc (suc n)))
    → fst b <ᵗ fst a
    → fst x a ≤' fst x b
  decreasingΔ' {n = n} (x , p , q , r) b = uncurry (elimℕ (λ _ → λ()) (λ a → indStep a (fst b ≟ᵗ a)))
    where
    indStep : (a : ℕ)
      → Trichotomyᵗ (fst b) a
      → ((y : a <ᵗ suc (suc n)) → fst b <ᵗ a → x (a , y) ≤' x b)
      → (y : a <ᵗ suc n) → fst b <ᵗ suc a → x (suc a , y) ≤' x b
    indStep a (lt s) indhyp a< ineq =
      IsPoset.is-trans (PosetStr.isPoset (snd (MeetSemilattice.IndPoset meetLattice)))
        (x (suc a , a<)) _ (x b)
        (cong₂ _∧l_ refl (cong x PathFin) ∙ r (a , a<))
        (indhyp (<ᵗ-trans a< <ᵗsucm) s)
    indStep a (eq s) indhyp a< ineq =
      cong₂ _∧l_ refl (cong x (Σ≡Prop (λ _ → isProp<ᵗ) s)) ∙ r (a , a<)
    indStep a (gt s) indhyp a< ineq = Empty.rec (falseDichotomies.gt-lt (s , ineq))

  decreasingΔ : {n : ℕ} (x : Δ n) (b a : Fin (suc (suc n)))
    → fst b ≤ᵗ fst a
    → fst x a ≤' fst x b
  decreasingΔ {n = n} x b a t with ((fst b) ≟ᵗ (fst a))
  ... | lt w = decreasingΔ' x b a w
  ... | eq w = cong₂ _∧l_ refl (cong (fst x) (Fin≡ _ _ w)) ∙ idem∧ _
  ... | gt w = Empty.rec (¬squeeze (w , t))

  ⟦_⟧ : {n : ℕ} → Δ n → (Fin (2 + n) → 𝐈)
  ⟦_⟧ = fst

  -- horn Λⁿₖ
  Λ : (n k : ℕ) → Type ℓ
  Λ n k = Σ[ x ∈ Δ n ] ∃[ j ∈ Fin (suc n) ]
          (¬ (fst j ≡ n ∸ k)) × (⟦ x ⟧ (injectSuc j) ≡ ⟦ x ⟧ (fsuc j))

  isSetΛ : {n k : ℕ} → isSet (Λ n k)
  isSetΛ {n = n} =
    isSetΣ isSetΔ λ _ → isProp→isSet squash₁


  -- horn inclusoins
  ƛ : (n k : ℕ) → Λ n k → Δ n
  ƛ n k = fst

  ΔPath : (n : ℕ) (x y : Δ n) → fst x ≡ fst y → x ≡ y
  ΔPath n x y p = Σ≡Prop (λ _ → isProp× (isSetI _ _)
                                (isProp× (isSetI _ _)
                                (isPropΠ λ _ → isSetI _ _))) p



  isSegal : (X : Type ℓ₁) → Type _
  isSegal X = ⦅ ƛ 2 1 ⦆ ⊥ ⦅ terminal* X ⦆

  SegalType : (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  SegalType ℓ = Σ[ X ∈ Type ℓ ] (isSegal X)

  isSegalFibration :  {X Y : Type ℓ} (p : Y → X) → Type ℓ
  isSegalFibration p = ⦅ ƛ 2 1 ⦆ ⊥ ⦅ p ⦆

  _! : ∀ {ℓ} (X : SegalType ℓ) → Map ℓ
  X ! = ⦅ terminal* (fst X) ⦆

  isInnerAnodyne : {ℓ' : Level} → Map ℓ' → Type _
  isInnerAnodyne i = (X : SegalType ℓ) → i ⊥ (X !)

  isInnerAnodyneFib : Map ℓ → Type _
  isInnerAnodyneFib i = {X Y : Type ℓ} (p : Y → X) → isSegalFibration p → i ⊥ ⦅ p ⦆

  -- Goal : Show (ƛ n k) is a retract of (ƛ n k) ⊠ᵐ (ƛ 2 1)

  -- definition of the section
  module _ (n k : ℕ) where
    Δ→Δ₂ : Δ n → Δ 2
    Δ→Δ₂ (f , l , m , r) .fst (zero , _) = 1l
    Δ→Δ₂ (f , l , m , r) .fst (suc zero , _) = f (n ∸ k , ∸-<ᵗ-suc n k)
    Δ→Δ₂ (f , l , m , r) .fst (suc (suc zero) , _) = f (suc (n ∸ k) , ∸-<ᵗ n k)
    Δ→Δ₂ (f , l , m , r) .fst (suc (suc (suc zero)) , _) = 0l
    Δ→Δ₂ (f , l , m , r) .snd .fst = refl
    Δ→Δ₂ (f , l , m , r) .snd .snd .fst = refl
    Δ→Δ₂ (f , l , m , r) .snd .snd .snd (zero , s) = ∧l-1l _
    Δ→Δ₂ (f , l , m , r) .snd .snd .snd (suc zero , s) =
      subst2 _≤'_ refl (cong f PathFin)
                       (r (n ∸ k , ∸-<ᵗ n k))
    Δ→Δ₂ (f , l , m , r) .snd .snd .snd (suc (suc zero) , s) = 0l-∧l _

    Λ→Δ₂ : Λ n k → Δ 2
    Λ→Δ₂ x = Δ→Δ₂ (fst x)

    -- the section
    λ→λ⊠ᵐλ₂,₁ : Map[ ⦅ ƛ n k ⦆ , ⦅ ƛ n k ⦆ ⊠ᵐ ⦅ ƛ 2 1 ⦆ ]
    λ→λ⊠ᵐλ₂,₁ .fst x = inl (x , Λ→Δ₂ x)
    λ→λ⊠ᵐλ₂,₁ .snd .fst x = x , Δ→Δ₂ x
    λ→λ⊠ᵐλ₂,₁ .snd .snd x = refl

  -- definition of the retraction (ƛ n k) ⊠ᵐ (ƛ 2 1) → (ƛ n k)
  module _ (n k : ℕ) where
  -- step one: map beween codomains Δ×Δ₂→Δ : cod ((ƛ n k) ⊠ᵐ (ƛ 2 1)) → cod (ƛ n k)
    -- underlying map
    Δ×Δ₂→Δ-map-helper : Δ n × Δ 2 → (i : Fin (suc (suc n)))
      → Trichotomyᵗ (fst i) (n ∸ k) → 𝐈
    Δ×Δ₂→Δ-map-helper ((x , p) , y , q) (i , s) (lt x₁) =
       x (i , <ᵗ-trans x₁ (∸-<ᵗ-suc n k)) ∨l y (1 , tt)
    Δ×Δ₂→Δ-map-helper ((x , p) , y , q) (i , s) (eq x₁) =
      x (i , subst (_<ᵗ suc (suc n)) (sym x₁)
                               (∸-<ᵗ-suc n k))
              ∨l y (1 , tt)
    Δ×Δ₂→Δ-map-helper ((x , p) , y , q) (i , s) (gt x₁) =
      x (i , s) ∧l y (2 , tt)

    Δ×Δ₂→Δ-map : Δ n × Δ 2 → Fin (suc (suc n)) → 𝐈
    Δ×Δ₂→Δ-map s i = Δ×Δ₂→Δ-map-helper s i (fst i ≟ᵗ (n ∸ k))

    -- underlying map sends 0 to 1
    Δ×Δ₂→Δ-0↦1 : (x : _) (y : _) → Δ×Δ₂→Δ-map (x , y) fzero ≡ 1l
    Δ×Δ₂→Δ-0↦1 (x , p) (y , q) with (0 ≟ᵗ (n ∸ k))
    ... | lt x₁ = cong (_∨l y (1 , tt)) (fst p) ∙ 1l-∨l _
    ... | eq x₁ = cong (_∨l y (1 , tt)) (fst p) ∙ 1l-∨l _

    -- underlying map sends 1 to 0
    Δ×Δ₂→Δ-1↦0 : (x : _) (y : _) → Δ×Δ₂→Δ-map (x , y) flast ≡ 0l
    Δ×Δ₂→Δ-1↦0 (x , (_ , p , _)) (y , (_ , q , _)) with (suc n ≟ᵗ (n ∸ k))
    ... | lt x₁ = Empty.rec (¬m<ᵗm {m = suc n} (<ᵗ-trans {n = suc n} x₁ (∸-<ᵗ n k)))
    ... | eq x₁ = Empty.rec (¬m<ᵗm {m = suc n} (subst (_<ᵗ suc n) (sym x₁) (∸-<ᵗ n k)))
    ... | gt x₁ = cong₂ _∧l_ (cong x (Σ≡Prop (λ _ → isProp<ᵗ) refl) ∙ p) refl
                ∙ 0l-∧l _

    -- underlying map sends 1 to 0
    Δ×Δ₂→Δ-decr : (x : _) (y : _) (i : Fin (suc n))
      → Δ×Δ₂→Δ-map (x , y) (fsuc i) ≤' Δ×Δ₂→Δ-map (x , y) (injectSuc i)
    Δ×Δ₂→Δ-decr (x , p) (y , q) (i , i<) with (i ≟ᵗ (n ∸ k)) | (suc i ≟ᵗ (n ∸ k))
    ... | lt x₁ | lt x₂ = sym (∨lRdist∧l _ _ _)
                        ∙ cong₂ _∨l_ (cong₂ _∧l_ (cong x PathFin) (cong x PathFin)
                                     ∙ p .snd .snd (i , i<)
                                     ∙ cong x PathFin) refl
    ... | lt x₁ | eq x₂ = sym (∨lRdist∧l _ _ _)
                        ∙ cong₂ _∨l_ (cong₂ _∧l_ (cong x PathFin) (cong x PathFin)
                                     ∙ p .snd .snd (i , i<)
                                     ∙ cong x PathFin) refl
    ... | lt x₁ | gt x₂ = Empty.rec (falseDichotomies.gt-lt (x₁ , x₂))
    ... | eq x₁ | lt x₂ = Empty.rec (falseDichotomies.lt-eq (x₂ , cong suc x₁))
    ... | eq x₁ | eq x₂ = Empty.rec (falseDichotomies.eq-eq (x₂ , cong suc x₁))
    ... | eq x₁ | gt x₂ =
       ∧lLdist∨l ((x (suc i , i<) ∧l y (2 , tt))) _ _
     ∙ cong₂ _∨l_ (sym (∧lAssoc _ _ _)
                 ∙ cong₂ _∧l_ refl (∧lComm (y (2 , tt)) _)
                 ∙ ∧lAssoc _ _ _
                 ∙ cong₂ _∧l_
                    (cong₂ (λ p q → x p ∧l x q) PathFin PathFin
                    ∙ snd (snd p) (i , i<)) refl
                    ∙ cong₂ _∧l_ (cong x refl) refl)
                  (sym (∧lAssoc _ _ _)
                  ∙ cong₂ _∧l_ refl (q .snd .snd (1 , tt)))
     ∙ sym (∧lRdist∨l _ _ _)
     ∙ cong₂ _∧l_ (idem∨ _) refl
    ... | gt x₁ | lt x₂ = Empty.rec (falseDichotomies.gt-lt
                                      (x₂ , <ᵗ-trans x₁ (<ᵗ-trans <ᵗsucm <ᵗsucm)))
    ... | gt x₁ | eq x₂ = Empty.rec (falseDichotomies.lt-eq (x₁ , sym x₂))
    ... | gt x₁ | gt x₂ =
        ∧lAssoc _ _ _
      ∙ cong₂ _∧l_ (sym (∧lAssoc _ _ _)
                 ∙ cong₂ _∧l_ refl (∧lComm _ _)
                 ∙ ∧lAssoc _ _ _) refl
      ∙ sym (∧lAssoc _ _ _)
      ∙ cong₂ _∧l_ (snd (snd p) (i , i<)) (idem∧ _)

    -- complete definition of map between codomains
    Δ×Δ₂→Δ : Δ n × Δ 2 → Δ n
    Δ×Δ₂→Δ (x , y) .fst = Δ×Δ₂→Δ-map (x , y)
    Δ×Δ₂→Δ (x , y) .snd .fst = Δ×Δ₂→Δ-0↦1 x y
    Δ×Δ₂→Δ (x , y) .snd .snd .fst = Δ×Δ₂→Δ-1↦0 x y
    Δ×Δ₂→Δ (x , y) .snd .snd .snd = Δ×Δ₂→Δ-decr x y

  -- Step 2: map between domains domains Δ×Δ₂→Δ : dom ((ƛ n k) ⊠ᵐ (ƛ 2 1)) → dom (ƛ n k)
    -- need some technical lemmas about when Δ×Δ₂→Δ in constant
  private
    Δ×Δ₂→Δ-constant₁ : (n k : ℕ) (x : Δ n) (y : _) (j : Fin (suc n))
      → ¬ fst j ≡ n ∸ k
      → fst x (injectSuc j) ≡ fst x (fsuc j)
      → Δ×Δ₂→Δ-map n k (x , y) (injectSuc j)
       ≡ Δ×Δ₂→Δ-map n k (x , y) (fsuc j)
    Δ×Δ₂→Δ-constant₁ n k (x , p) (y , q) (j , j<) w s
      with (j ≟ᵗ (n ∸ k)) | (suc j ≟ᵗ (n ∸ k))
    ... | lt x₁ | lt x₂ =
      cong (_∨l y (1 , tt)) (cong x PathFin ∙ s ∙ cong x PathFin)
    ... | lt x₁ | eq x₂ =
      cong (_∨l y (1 , tt)) (cong x PathFin ∙ s ∙ cong x PathFin)
    ... | lt x₁ | gt x₂ = Empty.rec (falseDichotomies.gt-lt (x₁ , x₂))
    ... | eq x₁ | lt x₂ = Empty.rec (falseDichotomies.lt-eq (x₂ , cong suc x₁))
    ... | eq x₁ | eq x₂ = Empty.rec (falseDichotomies.eq-eq (x₂ , cong suc x₁))
    ... | eq x₁ | gt x₂ = Empty.rec (w x₁)
    ... | gt x₁ | lt x₂ = Empty.rec (falseDichotomies.gt-lt
                                      (x₂ , <ᵗ-trans x₁ (<ᵗ-trans <ᵗsucm <ᵗsucm)))
    ... | gt x₁ | eq x₂ = Empty.rec (falseDichotomies.lt-eq (x₁ , sym x₂))
    ... | gt x₁ | gt x₂ = cong (_∧l y (2 , tt)) s


    Δ×Δ₂→Δ-constant₂ : (n k : ℕ) → (0 <ᵗ k) → (k <ᵗ n)
      → (x : _) (y : _)
      → fst y (2 , tt) ≡ fst y (3 , tt)
      → Δ×Δ₂→Δ-map n k (x , y) (injectSuc (n , <ᵗsucm))
       ≡ Δ×Δ₂→Δ-map n k (x , y) (fsuc (n , <ᵗsucm))
    Δ×Δ₂→Δ-constant₂ n k 0k kn (x , p) y r with (n ≟ᵗ (n ∸ k)) | (suc n ≟ᵗ (n ∸ k))
    ... | lt x₁ | t = Empty.rec (falseDichotomies.gt-lt (∸-<ᵗ n k , x₁))
    ... | eq x₁ | lt x₂ = Empty.rec (falseDichotomies.lt-eq (x₂ , cong suc x₁))
    ... | eq x₁ | eq x₂ = Empty.rec (falseDichotomies.eq-eq (x₂ , cong suc x₁))
    Δ×Δ₂→Δ-constant₂ (suc n) (suc k) 0k kn x y r | eq x₁ | gt x₂ =
      Empty.rec (¬m<ᵗm (subst (_<ᵗ suc n) (sym x₁) (∸-<ᵗ n k)))
    ... | gt x₁ | lt x₂ = Empty.rec (falseDichotomies.gt-lt
                                      (x₂ , <ᵗ-trans x₁ (<ᵗ-trans <ᵗsucm <ᵗsucm)))
    ... | gt x₁ | eq x₂ = Empty.rec (falseDichotomies.lt-eq (x₁ , sym x₂))
    ... | gt x₁ | gt x₂ =
        cong₂ _∧l_ refl (r ∙ fst (snd (snd y)))
      ∙ (∧l-0l _ ∙ sym (∧l-0l _ ))
      ∙ cong₂ _∧l_ refl (sym (r ∙ fst (snd (snd y))))

    Δ×Δ₂→Δ-constant₃ : (n k : ℕ) → (0 <ᵗ k) → (k <ᵗ n)
      → (x : _) (y : _)
      → _
      → (s : Trichotomyᵗ 0 (n ∸ k))
      → (t : Trichotomyᵗ 1 (n ∸ k))
      → Δ×Δ₂→Δ-map-helper n k (x , y) (0 , tt) s
       ≡ Δ×Δ₂→Δ-map-helper n k (x , y) (1 , tt) t
    Δ×Δ₂→Δ-constant₃ n k 0k kn x (y , q) s (lt x₁) (lt x₂) =
      sym (cong₂ _∨l_ refl (sym (fst q) ∙ s))
      ∙ (∨l-1l _ ∙ sym (∨l-1l _))
      ∙ cong₂ _∨l_ refl (sym (fst q) ∙ s)
    Δ×Δ₂→Δ-constant₃ n k 0k kn x (y , q) s (lt x₁) (eq x₂) =
      sym (cong₂ _∨l_ refl (sym (fst q) ∙ s))
      ∙ (∨l-1l _ ∙ sym (∨l-1l _))
      ∙ cong₂ _∨l_ refl (sym (fst q) ∙ s)
    Δ×Δ₂→Δ-constant₃ n k 0k kn x y s (lt x₁) (gt x₂) =
      Empty.rec (falseDichotomies.gt-lt (x₁ , x₂))
    Δ×Δ₂→Δ-constant₃ n k 0k kn x y s (eq x₁) t =
      Empty.rec (¬m<ᵗm (subst (k <ᵗ_) (lem n k kn x₁) kn))
      where
      lem : (n k : ℕ) → k <ᵗ n → 0 ≡ n ∸ k → (n ≡ k)
      lem (suc n) zero q r = sym r
      lem (suc n) (suc k) q r = cong suc (lem n k q r)

  -- complete definition of map between domains
  Dom[λ⊠ᵐλ₂₁]→Λ : (n k : ℕ) → (0 <ᵗ k) → (k <ᵗ n)
    → Dom (⦅ ƛ n k ⦆ ⊠ᵐ ⦅ ƛ 2 1 ⦆) → Λ n k
  Dom[λ⊠ᵐλ₂₁]→Λ n k 0k kn =
    rec∣inl (x , y) ↦ (Δ×Δ₂→Δ n k (fst x , y))
                     , PT.map (λ j → fst j , fst (snd j)
                                    , Δ×Δ₂→Δ-constant₁ n k (fst x) y (fst j)
                                                (fst (snd j)) (snd (snd j)))
                              (snd x)
       ∣inr (x , y) ↦ (Δ×Δ₂→Δ n k (x , fst y))
         , PT.map (λ { ((zero , j<) , p , q)
                     → fzero , snd (ineqlem₂ n k 0k kn)
                      , Δ×Δ₂→Δ-constant₃ n k 0k kn x (fst y) q _ _
                     ; ((suc zero , j<) , p , q) → Empty.rec (p refl)
                     ; ((suc (suc zero) , j<) , p , q)
                     → (n , <ᵗsucm) , (fst (ineqlem₂ n k 0k kn))
                     , Δ×Δ₂→Δ-constant₂ n k 0k kn x (fst y) q})
                  (snd y)
       ∣push (x , y) ↦ Σ≡Prop (λ _ → squash₁) refl
    where
    ineqlem₁ : (n k : ℕ) → 0 <ᵗ k → k <ᵗ suc n → 0 <ᵗ (suc n ∸ k)
    ineqlem₁ zero zero _ _ = tt
    ineqlem₁ (suc n) (suc k) p q with (k ≟ᵗ 0)
    ... | eq x = subst (0 <ᵗ_) (cong (suc n ∸_) (sym x)) tt
    ... | gt x = ineqlem₁ n k x q

    ineqlem₂ : (n k : ℕ) → 0 <ᵗ k → k <ᵗ n → (¬ n ≡ n ∸ k) × (¬ (0 ≡ n ∸ k))
    ineqlem₂ (suc n) (suc k) p q .fst r =
      ¬m<ᵗm {m = suc n} (subst (_<ᵗ (suc n)) (sym r) (∸-<ᵗ n k))
    ineqlem₂ (suc n) k p q .snd r = subst (0 <ᵗ_) (sym r) (ineqlem₁ n k p q)

  -- Definition of retraction
  λ⊠ᵐλ₂,₁→λ : (n k : ℕ) → 0 <ᵗ k → k <ᵗ n → Map[ ⦅ ƛ n k ⦆ ⊠ᵐ ⦅ ƛ 2 1 ⦆ , ⦅ ƛ n k ⦆ ]
  λ⊠ᵐλ₂,₁→λ n k p q .fst = Dom[λ⊠ᵐλ₂₁]→Λ n k p q
  λ⊠ᵐλ₂,₁→λ n k p q .snd .fst = Δ×Δ₂→Δ n k
  λ⊠ᵐλ₂,₁→λ n k p q .snd .snd =
      elimProp _ (λ _ → isSetΔ _ _)
                 (λ _ → refl)
                 (λ _ → refl)


  λ-retr-⊠ᵐ :  (n k : ℕ) → 0 <ᵗ k → k <ᵗ n → retractMap ⦅ ƛ n k ⦆ (⦅ ƛ n k ⦆ ⊠ᵐ ⦅ ƛ 2 1 ⦆)
  λ-retr-⊠ᵐ n k 0k kn .fst = λ→λ⊠ᵐλ₂,₁ n k
  λ-retr-⊠ᵐ n k 0k kn .snd .fst = λ⊠ᵐλ₂,₁→λ n k 0k kn
  λ-retr-⊠ᵐ n k 0k kn .snd .snd =
      ΣPathP (funExt retractS
    , ΣPathPProp (λ _ → isPropΠ λ _ → isSetΔ _ _)
              (funExt retractT))
    where
    retractProof : (n k : ℕ) → 0 <ᵗ k → k <ᵗ n
      → (x : Δ n) (t : _)
      → Δ×Δ₂→Δ-map n k (x , Δ→Δ₂ n k x) t ≡ x .fst t
    retractProof n k 0k kn (x , p) t with (fst t ≟ᵗ (n ∸ k))
    ... | lt x₁ = (cong₂ _∨l_ (cong x PathFin) refl ∙ ∨lComm _ _)
                ∙ Order.≤m→≤j (𝐈 , (latticestr 0l 1l _ _ isLattice))
                               (x (n ∸ k , ∸-<ᵗ-suc n k)) (x t)
                  (decreasingΔ (x , p) _ _ (<ᵗ-trans x₁ <ᵗsucm))
    ... | eq x₁ = cong₂ _∨l_ (cong x PathFin)
                             (cong x (Σ≡Prop (λ _ → isProp<ᵗ) (sym x₁)))
                             ∙ idem∨ _
    ... | gt x₁ = decreasingΔ (x , p) (suc (n ∸ k) , ∸-<ᵗ n k) t x₁

    retractT : (x : _) → Δ×Δ₂→Δ n k (x , Δ→Δ₂ n k x) ≡ x
    retractT x = Σ≡Prop isProp-hasΔStr (funExt (retractProof n k 0k kn x))

    retractS : (x : _) → Dom[λ⊠ᵐλ₂₁]→Λ n k 0k kn (inl (x , Λ→Δ₂ n k x)) ≡ x
    retractS x = Σ≡Prop (λ _ → squash₁) (retractT (fst x))

  isInnerAnodyneHornInclusion : (n k : ℕ) → 0 <ᵗ k → k <ᵗ n → isInnerAnodyne ⦅ ƛ n k ⦆
  isInnerAnodyneHornInclusion n k 0k kn (X , isSegalX) =
    retract⊥ _ ⦅ ƛ n k ⦆ ⦅ terminal* X ⦆
              (subst (retractMap ⦅ ƛ n k ⦆)
                     (invEq univalenceMap (comm⊠ᵐ _ _))
                     (λ-retr-⊠ᵐ n k 0k kn))
              (⊠⊥ _ _ _ isSegalX)

  isInnerAnodyneFibHornInclusion :
    (n k : ℕ) → 0 <ᵗ k → k <ᵗ n → isInnerAnodyneFib ⦅ ƛ n k ⦆
  isInnerAnodyneFibHornInclusion n k 0k kn p fb =
    retract⊥ _ ⦅ ƛ n k ⦆ ⦅ p ⦆
              (subst (retractMap ⦅ ƛ n k ⦆)
                     (invEq univalenceMap (comm⊠ᵐ _ _))
                     (λ-retr-⊠ᵐ n k 0k kn))
     (⊠⊥ _ _ _ fb)
