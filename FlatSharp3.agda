{-# OPTIONS --rewriting --without-K #-}

{-

To get Andrea Vezzosi's flat-ified Agda:

git clone https://github.com/agda/agda
cd agda
git checkout flat
cabal install --program-suffix=-flat

and then change your emacs startups to point to agda-flat and agda-mode-flat

-}

open import Agda.Primitive

module FlatSharp3 where

  -- library 

  data _==_ {l1 : Level} {A : Set l1} (a : A) : A → Set l1 where
    refl : a == a

  transport : ∀ {l1 l2 : Level} {A : Set l1} (C : A →  Set l2) {M N : A} (P : M == N) → C M → C N
  transport C refl x = x

  ap : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f refl = refl

  apc : ∀ {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} {B : Set l2} {M N :{♭} A}
       (f : (x :{♭} A) → B) → M == N → (f M) == (f N)
  apc f refl = refl

  -- ap2 :  {A B C : Set} {M N : A} {M' N' : B} (f : A -> B -> C) -> M == N -> M' == N' -> (f M M') == (f N N')
  -- ap2 f refl refl = refl

  ! : {l1 : Level} {A : Set l1} {M N : A} → M == N → N == M
  ! refl = refl

  _∘_  : {l1 : Level} {A : Set l1} {M N P : A} → N == P → M == N → M == P
  β ∘ refl = β

  record Σe {l1 l2 : Level} (A : Set l1) (B : A -> Set l2) : Set (l1 ⊔ l2) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σe public

  Σ : {l1 l2 : Level} {A : Set l1} -> (B : A -> Set l2) -> Set (l1 ⊔ l2)
  Σ {_}{_}{A} B = Σe A B

  infixr 0 _,_

  -- ----------------------------------------------------------------------

  data ♭ {l :{♭} Level} (A :{♭} Set l) : Set l where
    ♭i : (a :{♭} A) → ♭ A

  counit : ∀ {l :{♭} _} {A :{♭} Set l} → ♭ A → A
  counit (♭i x) = x

  ♭-elim : ∀ {c} {l :{♭} Level} {A :{♭} Set l}
         → (C : ♭ A → Set c)
         → ((u :{♭} A) → C (♭i u))
         → (x : ♭ A) → C x
  ♭-elim C f (♭i x) = f x

  -- crisp flat induction and crisp id induction are provable by pattern matching

  ♭-elim-crisp : ∀ {c} {l :{♭} Level} {A :{♭} Set l}
         → (C : (x :{♭} ♭ A) → Set c)
         → ((u :{♭} A) → C (♭i u))
         → (x :{♭} ♭ A) → C x
  ♭-elim-crisp C f (♭i x) = f x

  ff1 : {l :{♭} Level} {A :{♭} Set l} → ♭ (♭ A) → ♭ A
  ff1 (♭i (♭i x)) = ♭i x

  ff2 : {l :{♭} Level} {A :{♭} Set l} → ♭ A → ♭ (♭ A) 
  ff2 (♭i x) = ♭i (♭i x)

  ff3 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ A) → ff1 (ff2 x) == x
  ff3 (♭i x) = refl

  ff4 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ (♭ A)) → ff2 (ff1 x) == x
  ff4 (♭i (♭i x)) = refl

  path-ind-crisp : ∀ {l :{♭} Level} {A :{♭} Set l} {a :{♭} A}
         → (C : (y :{♭} A) (p : a == y) → Set l)
         → C a refl
         → (y :{♭} A) (p :{♭} a == y) → C y p
  path-ind-crisp C b _ refl = b


  -- ----------------------------------------------------------------------
  -- sharp

  postulate
    Rewrite : {l1 : Level} {A : Set l1} → A → A → Set l1
  {-# BUILTIN REWRITE Rewrite #-}

  -- postulate ♯ is a monadic modality
  postulate
    ♯  : {l : Level} (A : Set l) → Set l
    ♯i : {l : Level} {A : Set l} → A → ♯ A
    ♯-elim : {l1 l2 : Level} {A : Set l1} (C : ♯ A → Set l2) 
           → ((x : A) → ♯ (C (♯i x)))
           → ((x : ♯ A) → ♯ (C x))
    ♯-elim-β : {l1 l2 : Level} {A : Set l1} (C : ♯ A → Set l2) 
               → (f : (x : A) → ♯ (C (♯i x)))
               → (x : A) 
               → Rewrite (♯-elim C f (♯i x)) (f x)
    {-# REWRITE ♯-elim-β #-}

    -- really should be stated in terms of IsEquiv
    -- see Def 7.7.5 in the HoTT book
    ♯path : ∀ {l : Level} {A : Set l} {x y : ♯ A}
           → (x == y) == ♯ (x == y)
    coe-♯path-refl : ∀ {l : Level} {A : Set l} {x : ♯ A}
                   → transport (\ X → X) (♯path {x = x}{y = x}) refl == ♯i refl
  
  -- postulate that ♯ sees A as ♭ A
  postulate
    promote : {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} 
                (C : A → Set l2) 
              → ((x :{♭} A) → ♯ (C x))
              → (x : A) → ♯ (C x)
    promoteβ : {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} (C : A → Set l2) 
              → (f : (x :{♭} A) → ♯ (C x))
              → (x :{♭} A) → (promote C f x) == (f x)

  -- postulate ♭♯ fusion iso:
  -- judgemental version of "induced map ♭ A → ♭ (♯ A) is an equivalence" 
  postulate
    ♭♯e : {l :{♭} Level} {A :{♭} Set l} → (x :{♭} (♯ A)) → A
    ♭♯β : {l :{♭} Level} {A :{♭} Set l} (x :{♭} A) → Rewrite (♭♯e (♯i x)) x
    ♭♯η : {l :{♭} Level} {A :{♭} Set l} (x :{♭} ♯ A) → x == ♯i (♭♯e x)
    {-# REWRITE ♭♯β #-}
    -- coherence between β (which is a rewrite so definitional) and η
    ♭♯η-triangle : {l :{♭} Level} {A :{♭} Set l} (x :{♭} A) → ♭♯η (♯i x) == refl



  module FlatSharpIso where

    -- internalization of the postulates

    fs1 : {l :{♭} Level} {A :{♭} Set l} → ♭ (♯ A) → ♭ A
    fs1 = ♭-elim _ (\ u → ♭i (♭♯e u))
  
    fs2 : {l :{♭} Level} {A :{♭} Set l} → ♭ A → ♭ (♯ A) 
    fs2 (♭i x) = ♭i (♯i x)
  
    fs3 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ A) → fs1 (fs2 x) == x
    fs3 (♭i x) = refl
  
    fs4 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ (♯ A)) → fs2 (fs1 x) == x
    fs4 (♭i x) = apc ♭i (! ( (♭♯η x) ))


  module SharpFlatIso where

    -- "induced map ♯ (♭ A) → ♯ A is an equivalence" 
    
    -- follows from promote

    ♯counit : {l :{♭} Level} {A :{♭} Set l} → ♯ (♭ A) → ♯ A
    ♯counit = ♯-elim _ (\x → ♯i (counit x)) 

    ♯♭i : {l :{♭} Level} {A :{♭} Set l} → ♯ A → ♯ (♭ A)
    ♯♭i = ♯-elim _ (promote _ (\ x → ♯i (♭i x) ))

    ♯♭β : {l :{♭} Level} {A :{♭} Set l} (x : ♯ A) → (♯counit (♯♭i x)) == x
    ♯♭β x = transport (\ X → X) (! ♯path)
                      (♯-elim (\ x → (♯counit (♯♭i x) == x))
                              (promote _ (\ a → ♯i (ap (♯-elim _ (λ x₁ → ♯i (counit x₁)))
                                                       (promoteβ _ (\ x → ♯i (♭i x) ) a))))
                              x) 

    ♯♭η : {l :{♭} Level} {A :{♭} Set l} (x : ♯ (♭ A)) → (♯♭i (♯counit x)) == x
    ♯♭η x = transport (\ X → X) (! ♯path)
                      (♯-elim (\ x → (♯♭i (♯counit x) == x))
                              (♭-elim _ (\ a → ♯i (promoteβ _ _ a)))
                              x)
