module SOAS

import Data.List.Quantifiers
import Data.Singleton
import Data.DPair
import Syntax.WithProof

prefix 4 %%
infixr 3 -|> , -||> , ~> , ~:> , -<>, ^
infixl 3 <<<
infixr 4 :-

record (.extension) (types : Type) where
  constructor (:-)
  0 name : String
  ofType : types

data (.Ctx) : (type : Type) -> Type where
  Lin : type.Ctx
  (:<) : (ctx : type.Ctx) -> (namety : type.extension) -> type.Ctx

(.Family), (.SortedFamily) : Type -> Type
type.Family = type.Ctx -> Type
type.SortedFamily = type -> type.Family

data (.varPos) : type.Ctx -> (0 x : String) -> type -> Type
    where [search x]
  Here  : (ctx :< (x :- ty)).varPos x ty
  There : ctx.varPos x ty -> (ctx :< sy).varPos x ty

data (.var) : type.Ctx -> type -> Type where
  (%%) : (0 name : String) -> {auto pos : ctx.varPos name ty} -> ctx.var ty

0
(.name) : ctx.var ty -> String
(%% name).name = name

(.pos) : (v : ctx.var ty) -> ctx.varPos v.name ty
((%% name) {pos}).pos = pos

(.toVar) : (v : ctx.varPos x ty) -> ctx.var ty
pos.toVar {x} = (%% x) {pos}

ThereVar : (v : ctx.var ty) -> (ctx :< ex).var ty
ThereVar v = (%% v.name) {pos = There v.pos}

Var : type.SortedFamily
Var = flip (.var)

0
(-||>) : {type : Type} -> (src,tgt : type.Family) -> Type
(src -||> tgt) = {0 ctx : type.Ctx} -> src ctx -> tgt ctx

0
(-|>) : {type : Type} -> (src,tgt : type.SortedFamily) -> Type
(src -|> tgt) = {ty : type} -> src ty -||> tgt ty

(++) : (ctx1,ctx2 : type.Ctx) -> type.Ctx
ctx1 ++ [<] = ctx1
ctx1 ++ (ctx2 :< ty) = (ctx1 ++ ctx2) :< ty

(<<<) : type.SortedFamily -> type.Ctx -> type.SortedFamily
(f <<< ctx0) ty ctx = f ty (ctx ++ ctx0)

(.subst) : {type : Type} -> type.SortedFamily -> type.Ctx -> type.Ctx -> Type
f.subst ctx1 ctx2 = {ty : type} -> ctx1.var ty -> f ty ctx2

0 (.substNamed) : {type : Type} -> type.SortedFamily -> type.Ctx -> type.Ctx -> Type
f.substNamed ctx1 ctx2 = {0 x : String} -> {ty : type} -> ctx1.varPos x ty -> f ty ctx2

(~>) : {type : Type} -> (src, tgt : type.Ctx) -> Type
(~>) = (Var).subst

0 (~:>) : {type : Type} -> (src, tgt : type.Ctx) -> Type
(~:>) = (Var).substNamed

weakl : (ctx1, ctx2 : type.Ctx) -> ctx1 ~> (ctx1 ++ ctx2)
weakl ctx1 [<] x = x
weakl ctx1 (ctx2 :< z) x = ThereVar (weakl ctx1 ctx2 x)

weakrNamed : (ctx1, ctx2 : type.Ctx) -> ctx2 ~:> (ctx1 ++ ctx2)
weakrNamed ctx1 (ctx :< (x :- ty)) Here = (%% x) {pos = Here}
weakrNamed ctx1 (ctx :< sy) (There pos) =
  ThereVar $ weakrNamed ctx1 ctx pos

weakr : (ctx1, ctx2 : type.Ctx) -> ctx2 ~> (ctx1 ++ ctx2)
weakr ctx1 ctx2 ((%% name) {pos}) = weakrNamed ctx1 ctx2 pos

(.copairPos) : (0 x : type.SortedFamily) -> {ctx2 : type.Ctx} ->
  x.subst ctx1 ctx -> x.subst ctx2 ctx -> x.substNamed (ctx1 ++ ctx2) ctx
x.copairPos {ctx2 = [<]} g1 g2 pos = g1 $ pos.toVar
x.copairPos {ctx2 = (ctx :< (name :- ty))} g1 g2 Here = g2 (Here .toVar)
x.copairPos {ctx2 = (ctx2 :< namety)} g1 g2 (There pos) =
  x.copairPos g1 (g2 . ThereVar) pos

(.copair) : (0 x : type.SortedFamily) -> {ctx2 : type.Ctx} ->
  x.subst ctx1 ctx -> x.subst ctx2 ctx -> x.subst (ctx1 ++ ctx2) ctx
x.copair g1 g2 v = x.copairPos g1 g2 v.pos

extend : (0 x : type.SortedFamily) -> {0 ctx1 : type.Ctx} -> {ty : type} ->
  x ty ctx2 -> x.subst ctx1 ctx2 -> x.subst (ctx1 :< (n :- ty)) ctx2
extend x {ctx2, ty} u theta =
  x.copair {ctx2 = [< n :- ty]} theta workaround -- (\case {Here => x})
    where
      workaround : x.subst [< (n :- ty)] ctx2
      workaround ((%% _) {pos = Here}) = u
      workaround ((%% _) {pos = There _}) impossible

0
(-<>) : (src, tgt : type.SortedFamily) -> type.SortedFamily
(src -<> tgt) ty ctx = {0 ctx' : type.Ctx} -> src ty ctx' ->
  tgt ty (ctx ++ ctx')

-- TODO: (Setoid) coalgebras

0
(^) : (tgt, src : type.SortedFamily) -> type.SortedFamily
(tgt ^ src) ty ctx =
  {0 ctx' : type.Ctx} -> src.subst ctx ctx' -> tgt ty ctx'

0
Nil : type.SortedFamily -> type.SortedFamily
Nil f = f ^ Var

hideCtx : {0 a : type.Ctx -> Type} ->
  ((0 ctx : type.Ctx) -> a ctx) -> {ctx : type.Ctx} -> a ctx
hideCtx f {ctx} = f ctx

0
(*) : (derivative, tangent : type.SortedFamily) -> type.SortedFamily
(derivative * tangent) ty ctx =
  (ctx' : type.Ctx ** (derivative ty ctx' , tangent.subst ctx' ctx))

record MonStruct (m : type.SortedFamily) where
  constructor MkSubstMonoidStruct
  var : Var -|> m
  mult : m -|> (m ^ m)

(.sub) : {m : type.SortedFamily} -> {ty,sy : type} -> {ctx : type.Ctx} ->
  (mon : MonStruct m) => m sy (ctx :< (n :- ty)) -> m ty ctx -> m sy ctx
t.sub s = mon.mult t (extend m s mon.var)

(.sub2) : {m : type.SortedFamily} -> {ty1,ty2,sy : type} ->
  {ctx : type.Ctx} ->
  (mon : MonStruct m) => m sy (ctx :< (x :- ty1) :< (x :- ty2)) ->
  m ty1 ctx ->  m ty2 ctx -> m sy ctx
t.sub2 s1 s2 = mon.mult t (extend m s2 (extend m s1 mon.var))

record (.PointedCoalgStruct) type (x : type.SortedFamily) where
  constructor MkPointedCoalgStruct
  ren : x -|> [] x
  var : Var -|> x

liftPos : (ctx : type.Ctx) -> (mon : type.PointedCoalgStruct p) =>
  {ctx2 : type.Ctx} ->
  (p.subst ctx1 ctx2) -> p.substNamed (ctx1 ++ ctx) (ctx2 ++ ctx)
liftPos [<] f x = f x.toVar
liftPos (ctx :< (_ :- _)) f Here = mon.var (Here .toVar)
liftPos (ctx :< namety) f (There pos) = mon.ren (liftPos ctx f pos)
  ThereVar


lift : (ctx : type.Ctx) -> (mon : type.PointedCoalgStruct p) =>
  {ctx2 : type.Ctx} ->
  (p.subst ctx1 ctx2) -> p.subst (ctx1 ++ ctx) (ctx2 ++ ctx)
lift ctx f v = liftPos ctx f v.pos

0
(.SortedFunctor) : (type : Type) -> Type
type.SortedFunctor = type.SortedFamily -> type.SortedFamily

0
Strength : (f : type.SortedFunctor) -> Type
Strength f = {0 p,x : type.SortedFamily} -> (mon : type.PointedCoalgStruct p) =>
  (f (x ^ p)) -|> ((f x) ^ p)

0
(.Map) : type.SortedFunctor -> Type
signature.Map
  = {0 a,b : type.SortedFamily} -> (a -|> b) ->
    signature a -|> signature b

record (.MonoidStruct)
         (signature : type.SortedFunctor)
         (x : type.SortedFamily) where
  constructor MkSignatureMonoid
  mon : MonStruct x
  alg : signature x -|> x

record (.MetaAlg)
         (signature : type.SortedFunctor)
         (meta : type.SortedFamily)
         (a : type.SortedFamily) where
  constructor MkMetaAlg
  alg : signature a -|> a
  var : Var -|> a
  mvar : meta -|> (a ^ a)


traverse : {0 p,a : type.SortedFamily} ->
      {0 signature : type.SortedFunctor} ->
      (functoriality : signature.Map) =>
      (str : Strength signature) =>
      (coalg : type.PointedCoalgStruct p) =>
      (alg : signature a -|> a) ->
      (phi : p -|> a) ->
      (chi : meta -|> (a ^ a)) -> signature.MetaAlg meta (a ^ p)
traverse {p,a} alg phi chi = MkMetaAlg
      { alg = \h,s => alg $ str h s
      , var = \v,s => phi (s v)
      , mvar = \m,e,s => chi m (\v => e v s)
      }

-- Does this follow from everything else?
mapSubstPos : {0 a,b : type.SortedFamily} -> (a -|> b) -> {0 ctx : type.Ctx} ->
  {0 ctx' : type.Ctx} ->
  a.subst ctx ctx' -> b.substNamed ctx ctx'
mapSubstPos f {ctx = (ctx :< (x :- ty))} theta Here
  = f $ theta {ty} $ (%% _) {pos = Here}
mapSubstPos f {ctx = (ctx :< sy)} theta (There pos)
  = mapSubstPos {a,b} f (theta . ThereVar) pos

mapSubst : {0 a,b : type.SortedFamily} -> (a -|> b) -> {0 ctx : type.Ctx} ->
   (a.subst ctx -||> b.subst ctx)
mapSubst f {ctx = ctx0} theta v = mapSubstPos {a,b} f theta v.pos

(.MetaCtx) : Type -> Type
type.MetaCtx = SnocList (type.Ctx, type)

(.metaEnv) : type.SortedFamily -> type.MetaCtx -> type.Family
x.metaEnv [<]            ctx = ()
x.metaEnv (mctx :< meta) ctx =
  (x.metaEnv mctx ctx, (x <<< (fst meta)) (snd meta) ctx)

{- alas, non obviously strictly positive because we can't tell
   Idris that signature must be strictly positive.

   It will be, though, if we complete the termination project
-}

data (.Term) : (signature : type.SortedFunctor) ->
               type.SortedFamily -> type.SortedFamily where
  Op : {0 signature : type.SortedFunctor} ->
       signature (signature.Term x) ty ctx ->
       signature.Term x ty ctx
  Va : Var ty ctx -> signature.Term x ty ctx
  Me : {0 ctx1, ctx2 : type.Ctx} ->
       {0 signature : type.SortedFunctor} ->
       x ty ctx2 ->
       (signature.Term x).subst ctx2 ctx1 ->
       signature.Term {type} x ty ctx1

(.sem) : (0 a : type.SortedFamily) ->
         {0 signature : type.SortedFunctor} ->
         (functoriality : signature.Map) =>
         (str : Strength signature) =>
         (metalg : signature.MetaAlg x a) =>
         signature.Term x -|> a
a.sem (Op args) = metalg.alg
                 $ functoriality {b = a}
                   (a.sem {signature,x,str,functoriality}) args
a.sem (Va x   ) = MetaAlg.var metalg x
a.sem (Me  m env)
  = MetaAlg.mvar metalg m
  $ mapSubst {a=signature.Term x, b = a}
    (a.sem {signature,x,str,functoriality})
    env

(.envSem) : (0 a : type.SortedFamily) ->
            {0 signature : type.SortedFunctor} ->
            (str : Strength signature) =>
            (functoriality : signature.Map) =>
            (metalg : signature.MetaAlg x a) =>
            {mctx : type.MetaCtx} ->
            (signature.Term x).metaEnv mctx ctx ->
                             a.metaEnv mctx ctx

a.envSem {mctx = [<]         } menv = ()
a.envSem {mctx = mctx :< meta} (menv,v) =
      ( a.envSem {signature,x,str,functoriality} menv
      , a.sem {signature,x,str,functoriality} v
      )

(.TermAlg) :
  (0 signature : type.SortedFunctor) ->
  (str : Strength signature) =>
  (functoriality : signature.Map) =>
  (0 x : type.SortedFamily) ->
  signature.MetaAlg x (signature.Term x)
signature.TermAlg x = MkMetaAlg
  { alg = Op
  , mvar = \m => Me m  -- bug: type-checker complains if we
                       -- eta-reduce
  , var = Va
  }

-- Not sure these are useful
data (+) : (signature1, signature2 : type.SortedFunctor) ->
  type.SortedFunctor where
  Lft  :  {signature1, signature2 : type.SortedFunctor} ->
    (op : sig1 x ty ctx) -> (sig1 + sig2) x ty ctx
  Rgt :  {signature1, signature2 : type.SortedFunctor} ->
    (op : sig2 x ty ctx) -> (sig1 + sig2) x ty ctx

sum : (signatures : List $ (String, type.SortedFunctor)) ->
  type.SortedFunctor
(sum signatures) x ty ctx = Any (\(name,sig) => sig x ty ctx) signatures

prod : (signatures : List $ type.SortedFunctor) ->
  type.SortedFunctor
(prod signatures) x ty ctx = All (\sig => sig x ty ctx) signatures

bind : (tys : type.Ctx) -> type.SortedFunctor
bind tys = (<<< tys)

infixr 3 -:>

-- Writing the descriptions directly is fine
-- but deriving their functoriality and strength is annoying
-- and not needed with enough metaprogramming

data TypeSTLC = B | (-:>) TypeSTLC TypeSTLC

data STLC : TypeSTLC .SortedFunctor  where
  App : {ty1, ty2 : TypeSTLC} ->
        (f : a (ty1 -:> ty2) ctx) ->
        (x : a ty1 ctx) -> STLC a ty2 ctx
  Lam : (x : String) -> {ty1 : TypeSTLC} ->
        (body : a ty2 (ctx :< (x :- ty1))) ->
        STLC a (ty1 -:> ty2) ctx

%hint
strSTLC : Strength STLC
strSTLC               (App f x           ) theta
  = App (f theta) (x theta)
strSTLC {p, mon, ctx} (Lam str {ty1} body) theta
  = Lam str $ body $ extend p (mon.var (%% str))
  $ \v => mon.ren (theta v)
                  (\u => ThereVar u) -- Bug: can't eta-reduce

%hint
functorialitySTLC : STLC .Map
functorialitySTLC h (App f x) = App (h f) (h x)
functorialitySTLC h (Lam str body) = Lam str (h body)

Ex1 : STLC .Term Var (B -:> (B -:> B) -:> B) [<]
Ex1 = Op $ Lam "x" $
      Op $ Lam "f" $
      Op $ App (Va $ %% "f")
               (Va $ %% "x")

beta : Singleton
       {a = STLC .Term Var ty ctx}
       (Op $ App (Op $ Lam x body) t) -> STLC .Term Var ty ctx
beta (Val .(Op $ App (Op $ Lam x body) t)) =
  ?beta_rhs

Ex2 : STLC .Term Var (B -:> B) [<]
Ex2 = Op $ App
        (Op $ Lam "f" $
         Op $ Lam "x" $
         Op $ App
              (Va $ %% "f")
              (Va $ %% "x"))
        (Op $ Lam "x" $
              Va $ %% "x")

Ex3 : STLC .Term Var (B -:> B) [<]
Ex3 = beta $ Val Ex2
