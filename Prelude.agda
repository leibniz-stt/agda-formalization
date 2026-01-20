{-# OPTIONS --cubical --guardedness #-}
{-

This file contains basic results and constructions that weren't (but
probably should be) in the Cubical library.

-}

module Prelude where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport

open import Cubical.Foundations.Equiv
 
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Inductive


open import Cubical.HITs.Pushout
open import Cubical.HITs.Join
  renaming (join to join') renaming (joinPushout to join)

open Iso

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A X : Type ℓ
    B Y : Type ℓ'
    C : Type ℓ''
    D : Type ℓ'''


--- Some syntax for pushout recursors/eliminators
infix 2 pushoutRecSyntax pushoutElimSyntax

syntax pushoutRecSyntax (λ x → l) (λ y → r) (λ z → p) =
  rec∣inl x ↦ l
     ∣inr y ↦ r
     ∣push z ↦ p

syntax pushoutElimSyntax (λ x → l) (λ y → r) (λ z → p) =
  elim∣inl x ↦ l
      ∣inr y ↦ r
      ∣push z ↦ p

pushoutRecSyntax : {f : A → B} {g : A → C}
  (l : B → D) (r : C → D) (p : (x : A) → l (f x) ≡ r (g x))
  → Pushout f g → D
pushoutRecSyntax l r p (inl x) = l x
pushoutRecSyntax l r p (inr x) = r x
pushoutRecSyntax l r p (push a i) = p a i

pushoutElimSyntax : ∀ {ℓ} {f : A → B} {g : A → C} {D : Pushout f g → Type ℓ}
  (l : (b : B) → D (inl b)) (r : (c : C) → D (inr c))
  (p : (x : A) → PathP (λ i → D (push x i)) (l (f x)) (r (g x)))
  (x : Pushout f g) → D x
pushoutElimSyntax l r p (inl x) = l x
pushoutElimSyntax l r p (inr x) = r x
pushoutElimSyntax l r p (push a i) = p a i

--- Homotopies
_∼_ : {B : A → Type ℓ} (f g : (x : A) → B x) → Type _
f ∼ g = (x : _) → f x ≡ g x

-- Constant maps
Const : (f : A → B) → Type _
Const {A = A} {B = B} f = Σ[ b ∈ B ] ((a : A) → f a ≡ b)

-- Characterisation of total space of the Const predicate
TotConstIso : Iso (Σ[ f ∈ (A → B) ] (Const f)) B
TotConstIso .fun (F , b , p) = b
TotConstIso .inv b = (const b) , (b , (λ _ → refl))
TotConstIso .sec _ = refl
TotConstIso .ret (F , b , p) =
  ΣPathP ((funExt (λ a → sym (p a)))
         , (ΣPathP (refl , (λ j a i → p a (~ j ∨ i)))))

-- Fibres of fst projections from ΣAB are isomorphic to fibres of B
Iso-fibFst-fib : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (a : A)
  → Iso (fiber (fst {B = B}) a) (B a)
Iso-fibFst-fib {B = B} a .fun (s , t) = subst B t (snd s)
Iso-fibFst-fib a .inv t = (a , t) , refl
Iso-fibFst-fib a .sec t = transportRefl t
Iso-fibFst-fib {B = B} a .ret = uncurry λ {(s , b) q
  → J (λ a q → ((a , subst B q b) , (λ _ → a)) ≡ ((s , b) , q))
      (ΣPathP ((ΣPathP (refl , transportRefl b)) , refl)) q}

-- Contracting away a (contractible) first entry of a Σ-type (with
-- choice of point of contractoin)
Σ-contractFstIso' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  (c : isContr A) (a : A) → Σ A B ≃ B a
Σ-contractFstIso' {B = B} c a =
  compEquiv (isoToEquiv (Σ-contractFstIso c)) (substEquiv B (snd c a))

-- Total space of (A ≃_) is contractible
isContrTot≃ : ∀ {ℓ} (A : Type ℓ) → isContr (Σ[ A' ∈ Type ℓ ] A ≃ A')
isContrTot≃ A .fst = A , idEquiv _
isContrTot≃ A .snd = lem _
  where
  lem = isOfHLevelRetractFromIso 1
         (Σ-cong-iso-snd λ A' → equivToIso (invEquiv univalence))
          (isContr→isProp (isContrSingl A))

-- Recursor for joins
joinPushout→ : (f : A → B) (g : C → D) → join A C → join B D
joinPushout→ f g =
  rec∣inl a ↦ inl (f a)
     ∣inr c ↦ inr (g c)
     ∣push ac ↦ push ((f (fst ac)) , g (snd ac))

Iso-join-joinPushout : Iso (join' A B) (join A B)
Iso-join-joinPushout .fun (inl x) = inl x
Iso-join-joinPushout .fun (inr x) = inr x
Iso-join-joinPushout .fun (push a b i) = push (a , b) i
Iso-join-joinPushout .inv (inl x) = inl x
Iso-join-joinPushout .inv (inr x) = inr x
Iso-join-joinPushout .inv (push (a , b) i) = push a b i
Iso-join-joinPushout .sec (inl x) = refl
Iso-join-joinPushout .sec (inr x) = refl
Iso-join-joinPushout .sec (push a i) = refl
Iso-join-joinPushout .ret (inl x) = refl
Iso-join-joinPushout .ret (inr x) = refl
Iso-join-joinPushout .ret (push a b i) = refl

module _ where
  private
    pushfill : ∀ {ℓ} (A : Type ℓ) (x y : A) (p : x ≡ y) (z : _) (q : y ≡ z)
      (r : x ≡ z) (sq : Square refl r (sym p) q) (i j k : I)
      → A
    pushfill A x y p z q r sq i j k =
      hfill (λ k → λ {(i = i0) → p (j ∧ ~ k)
                     ; (i = i1) → q (~ j)
                     ; (j = i0) → r i
                     ; (j = i1) → p (i ∨ ~ k)})
            (inS (sq (~ j) i)) k

  joinAssoc→ : join A (join B C) → join (join A B) C
  joinAssoc→ (inl x) = inl (inl x)
  joinAssoc→ (inr (inl x)) = inl (inr x)
  joinAssoc→ (inr (inr x)) = inr x
  joinAssoc→ (inr (push (b , c) i)) = push (inr b , c) i
  joinAssoc→ (push (a , inl x) i) = inl (push (a , x) i)
  joinAssoc→ (push (a , inr x) i) = push (inl a , x) i
  joinAssoc→ {A = A} {B = B} {C = C} (push (a , push (b , c) j) i) =
    pushfill (join (join A B) C) _ _ (push (inl a , c))
           _ (sym (push (inr b , c))) (λ i → inl (push (a , b) i))
           (λ i j → push (push (a , b) j , c) (~ i)) i j i1

  joinAssoc← : join (join A B) C → join A (join B C)
  joinAssoc← (inl (inl x)) = inl x
  joinAssoc← (inl (inr x)) = inr (inl x)
  joinAssoc← (inl (push (a , b) i)) = push (a , inl b) i
  joinAssoc← (inr x) = inr (inr x)
  joinAssoc← (push (inl x , c) i) = push (x , inr c) i
  joinAssoc← (push (inr x , c) i) = inr (push (x , c) i)
  joinAssoc← {A = A} {B = B} {C = C} (push (push (a , b) j , c) i) =
    pushfill (join A (join B C)) _ _ (sym (push (a , inr c))) _
      (push (a , inl b)) (λ i → inr (push (b , c) (~ i)))
      (λ i j → push (a , push (b , c) (~ j)) i) (~ i) (~ j) i1

  joinAssocIso : Iso (join A (join B C)) (join (join A B) C)
  joinAssocIso .fun = joinAssoc→
  joinAssocIso .inv = joinAssoc←
  joinAssocIso .sec (inl (inl x)) = refl
  joinAssocIso .sec (inl (inr x)) = refl
  joinAssocIso .sec (inl (push a i)) = refl
  joinAssocIso .sec (inr x) = refl
  joinAssocIso .sec (push (inl x , c) i) = refl
  joinAssocIso .sec (push (inr x , c) i) = refl
  joinAssocIso {A = A} {B = B} {C = C} .sec (push (push (a , b) j , c) i) k =
    hcomp (λ r →
    λ {(i  = i0) → inl (push (a , b) j)
     ; (i = i1) → push (inl a , c) (j ∨ r ∨ k)
     ; (j = i0) → push (inl a , c) (i ∧ (r ∨ k))
     ; (j = i1) → push (inr b , c) i
     ; (k = i0) → joinAssoc→
                    (pushfill (join A (join B C)) _ _
                      (sym (push (a , inr c))) _
                      (push (a , inl b))
                      (λ i → inr (push (b , c) (~ i)))
                      (λ i j → push (a , push (b , c) (~ j)) i)
                      (~ i) (~ j) r)
     ; (k = i1) →  push (push (a , b) j , c) i})
     (hcomp (λ r →
     λ {(i = i0) → inl (push (a , b) j)
      ; (i = i1) → push (inl a , c) (j ∨ ~ r ∨ k)
      ; (j = i0) → push (inl a , c) (i ∧ (~ r ∨ k))
      ; (j = i1) → push (inr b , c) i
      ; (k = i1) → push (push (a , b) j , c) i})
      (push (push (a , b) j , c) i))
  joinAssocIso .ret (inl x) = refl
  joinAssocIso .ret (inr (inl x)) = refl
  joinAssocIso .ret (inr (inr x)) = refl
  joinAssocIso .ret (inr (push a i)) = refl
  joinAssocIso .ret (push (a , inl x) i) = refl
  joinAssocIso .ret (push (a , inr x) i) = refl
  joinAssocIso {A = A} {B = B} {C = C} .ret (push (a , push (b , c) j) i) k =
    hcomp (λ r →
     λ {(i  = i0) → push (a , inr c) (j ∧ ~ r ∧ ~ k)
      ; (i = i1) → inr (push (b , c) j)
      ; (j = i0) → push (a , inl b) i
      ; (j = i1) → push (a , inr c) ((~ r ∧ ~ k) ∨ i)
      ; (k = i0) → joinAssoc←
          (pushfill (join (join A B) C) _ _ (push (inl a , c))
           _ (sym (push (inr b , c))) (λ i → inl (push (a , b) i))
           (λ i j → push (push (a , b) j , c) (~ i)) i j r)
      ; (k = i1) → push (a , push (b , c) j) i})
    (hcomp (λ r →
     λ {(i = i0) → push (a , inr c) (j ∧ ~ k ∧ r)
      ; (i = i1) → inr (push (b , c) j)
      ; (j = i0) → push (a , inl b) i
      ; (j = i1) → push (a , inr c) ((r ∧ ~ k) ∨ i)
      ; (k = i1) → push (a , push (b , c) j) i})
      (push (a , push (b , c) j) i))


joinCommFun : join A B → join B A
joinCommFun =
  rec∣inl x ↦ inr x
      ∣inr x ↦ inl x
      ∣push (a , b) ↦ sym (push (b , a))

joinCommFun² : (x : join A B) → joinCommFun (joinCommFun x) ≡ x
joinCommFun² =
  elim∣inl x ↦ refl
      ∣inr x ↦ refl
      ∣push (a , b) ↦ λ _ → refl

joinCommIso : Iso (join A B) (join B A)
joinCommIso .fun = joinCommFun
joinCommIso .inv = joinCommFun
joinCommIso .sec = joinCommFun²
joinCommIso .ret = joinCommFun²

-- Function space of joins
characJoinElim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : join A B → Type ℓ''}
  → Iso ((a : join A B) → C a)
        (Σ[ l ∈ ((a : A) → C (inl a)) ]
         Σ[ r ∈ ((b : B) → C (inr b)) ]
         ((a : A) (b : B)
           → PathP (λ i → C (push (a , b) i)) (l a) (r b)))
characJoinElim .Iso.fun f = (f ∘ inl) , ((f ∘ inr)
  , (λ a b → cong f (push (a , b))))
characJoinElim .Iso.inv (l , r , s) =
  elim∣inl x ↦ l x
      ∣inr x ↦ r x
      ∣push x ↦ s (fst x) (snd x)
characJoinElim .Iso.sec _ = refl
characJoinElim .Iso.ret f = funExt
  (elim∣inl x ↦ refl
       ∣inr x ↦ refl
       ∣push x ↦ λ i → refl)

-- Non-dependent version
characJoinRec : Iso (join A B → C)
                    (Σ[ l ∈ (A → C) ]
                     Σ[ r ∈ (B → C) ]
                     ((a : A) (b : B) → (l a) ≡ (r b)))
characJoinRec = characJoinElim

-- Alternative characterisation in terms of const

-- Biimplication
_↔_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A ↔ B = (A → B) × (B → A)

-- Equational reasoning for isos
step-Iso : (A : Type ℓ) → Iso A B → Iso B C → Iso A C
step-Iso A = compIso

infixr 2 step-Iso
syntax step-Iso A e e2 = A ≅⟨ e ⟩ e2

_□ : (A : Type ℓ) → Iso A A
_ □ = idIso

-- Equational reasoning for equiv
-- step-Equiv : (A : Type ℓ) → A ≃ B → B ≃ C → A ≃ C
-- step-Equiv A = compEquiv

-- infixr 3 step-Equiv
-- syntax step-Equiv A e e2 = A ≃⟨ e ⟩ e2

-- _◼ : (A : Type ℓ) → A ≃ A
-- _ ◼ = idEquiv _

codomainEquivDep : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
                 → ((a : A) → (B a) ≃ (C a))
                 → ((a : A) → B a) ≃ ((a : A) → C a)
codomainEquivDep e = isoToEquiv (codomainIsoDep (λ a → equivToIso (e a)))

swapArgsEquiv : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''}
  → ((a : A) (b : B) → C a b) ≃ ((b : B) (a : A) → C a b)
swapArgsEquiv =
  isoToEquiv (iso (λ F b a → F a b) (λ F b a → F a b)
                  (λ _ → refl) (λ _ → refl))

domEquivDep : ∀ {ℓ ℓ'} {A A' : Type ℓ}{B : A → Type ℓ'}
  → (e : A' ≃ A) 
  → ((a : A) → B a) ≃ ((a' : A') → B (fst e a'))
domEquivDep {A = A} {B = B} =
  EquivJ (λ A' e → ((a : A) → B a) ≃ ((a' : A') → B (fst e a'))) (idEquiv _)

terminal* : ∀ {ℓ} (X : Type ℓ) → X → Unit* {ℓ = ℓ}
terminal* X x = tt*

∸-<ᵗ : (n k : ℕ) → (n ∸ k) <ᵗ suc n
∸-<ᵗ n zero = <ᵗsucm {n}
∸-<ᵗ zero (suc k) = tt
∸-<ᵗ (suc n) (suc k) =
  <ᵗ-trans {n ∸ k} {suc n} {suc (suc n)} (∸-<ᵗ n k) (<ᵗsucm {suc n})

∸-<ᵗ-suc : (n k : ℕ) → (n ∸ k) <ᵗ suc (suc n)
∸-<ᵗ-suc n k = ∸-<ᵗ (suc n) (suc k)

-- slightly alternative definition of the function type over joins  
JoinFun≃ConstL : (join A B → C) ≃ (Σ[ f ∈ (A → C) ] (B → Const f))
JoinFun≃ConstL {A = A} {B = B} {C = C} =
  compEquiv (isoToEquiv characJoinRec)
     (Σ-cong-equiv-snd main)
  where
  main : (f : A → C)
    → (Σ[ r ∈ (B → C) ] ((a : A) (b : B) → (f a) ≡ (r b)))
     ≃ (B → Const f)
  main f = compEquiv (Σ-cong-equiv-snd (λ r → swapArgsEquiv))
            (invEquiv (Σ-Π-≃ {C = λ b c → (a : A) → f a ≡ c}))

JoinFun≃ConstR : (join A B → C) ≃ (Σ[ g ∈ (B → C) ] (A → Const g))
JoinFun≃ConstR {A = A} {B = B} {C = C} =
  compEquiv (isoToEquiv (domIso joinCommIso)) JoinFun≃ConstL
