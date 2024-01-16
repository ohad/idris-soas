module SOAS

import Data.List.Quantifiers

parameters {Ty : Type}
  data Ctx : Type where
    Lin : Ctx
    (:<) : (ctx : Ctx) -> (ty : Ty) -> Ctx

  data (.var) : Ctx -> Ty -> Type where
    Here  : (ctx :< ty).var ty
    There : ctx.var ty -> (ctx :< sy).var ty

  Family, SortedFamily : Type
  Family = Ctx -> Type
  SortedFamily = Ty -> Family

  Var : SortedFamily
  Var = flip (.var)

  infixr 3 -|> , ~> , -<>, ^

  infixl 3 <<<

  (-|>) : (src,tgt : SortedFamily) -> Type
  (src -|> tgt) = {ty : Ty} -> {ctx : Ctx} -> src ty ctx -> tgt ty ctx

  (++) : (ctx1,ctx2 : Ctx) -> Ctx
  ctx1 ++ [<] = ctx1
  ctx1 ++ (ctx2 :< ty) = (ctx1 ++ ctx2) :< ty

  (<<<) : SortedFamily -> Ctx -> SortedFamily
  (f <<< ctx0) ty ctx = f ty (ctx ++ ctx0)

  (.subst) : SortedFamily -> Ctx -> Ctx -> Type
  f.subst ctx1 ctx2 = {ty : Ty} -> ctx1.var ty -> f ty ctx2

  (~>) : (src, tgt : Ctx) -> Type
  (~>) = (flip (.var)).subst

  weakl : (ctx1, ctx2 : Ctx) -> ctx1 ~> (ctx1 ++ ctx2)
  weakl ctx1 [<] x = x
  weakl ctx1 (ctx2 :< z) x = There $ weakl ctx1 ctx2 x

  weakr : (ctx1, ctx2 : Ctx) -> ctx2 ~> (ctx1 ++ ctx2)
  weakr ctx1 (ctx2 :< _) Here = Here
  weakr ctx1 (ctx2 :< sy) (There x) = There (weakr ctx1 ctx2 x)

  (.copair) : (f : SortedFamily) -> {ctx2 : Ctx} -> f.subst ctx1 ctx -> f.subst ctx2 ctx -> f.subst (ctx1 ++ ctx2) ctx
  f.copair {ctx2 = [<]       } g1 g2 x = g1 x
  f.copair {ctx2 = ctx2 :< ty} g1 g2 Here = g2 Here
  f.copair {ctx2 = ctx2 :< ty} g1 g2 (There x) = f.copair g1 (g2 . There) x

  extend : (f : SortedFamily) -> {ctx1 : Ctx} -> {ty : Ty} -> f ty ctx2 -> f.subst ctx1 ctx2 -> f.subst (ctx1 :< ty) ctx2
  extend f {ctx2, ty} x theta = f.copair {ctx2 = [< ty]} theta workaround -- (\case {Here => x})
    where
      workaround : f.subst [< ty] ctx2
      workaround Here = x

  (-<>) : (src, tgt : SortedFamily) -> SortedFamily
  (src -<> tgt) ty ctx = {ctx' : Ctx} -> src ty ctx' -> tgt ty (ctx ++ ctx')


  Nil : SortedFamily -> SortedFamily
  Nil f ty ctx = {ctx' : Ctx} -> ctx ~> ctx' -> f ty ctx'

  -- TODO: (Setoid) coalgebras

  (^) : (tgt, src : SortedFamily) -> SortedFamily
  (tgt ^ src) ty ctx = {ctx' : Ctx} -> src.subst ctx ctx' -> tgt ty ctx'

  hideCtx : {0 a : Ctx -> Type} ->
    ((ctx : Ctx) -> a ctx) -> {ctx : Ctx} -> a ctx
  hideCtx f {ctx} = f ctx

  (*) : (derivative, tangent : SortedFamily) -> SortedFamily
  (derivative * tangent) ty ctx = (ctx' : Ctx ** (derivative ty ctx' , tangent.subst ctx' ctx))

record MonStruct {Ty : Type} (m : SortedFamily {Ty}) where
  constructor MkSubstMonoidStruct
  var : Var -|> m
  mult : m -|> (m ^ m)

(.sub) : {Ty : Type} -> {m : SortedFamily {Ty}} -> {ty,sy : Ty} -> {ctx : Ctx {Ty}} ->
  (mon : MonStruct m) => m sy (ctx :< ty) -> m ty ctx -> m sy ctx
t.sub s = mon.mult t (extend m s mon.var)

(.sub2) : {Ty : Type} -> {m : SortedFamily {Ty}} -> {ty1,ty2,sy : Ty} -> {ctx : Ctx {Ty}} ->
  (mon : MonStruct m) => m sy (ctx :< ty1 :< ty2) -> m ty1 ctx -> m ty2 ctx -> m sy ctx
t.sub2 s1 s2 = mon.mult t (extend m s2 (extend m s1 mon.var))

record PointedCoalgStruct (x : SortedFamily) where
  constructor MkPointedCoalgStruct
  ren : x -|> [] x
  var : Var -|> x

lift : (ctx : Ctx) -> (mon : PointedCoalgStruct p) => {ctx2 : Ctx} ->
  (p.subst ctx1 ctx2) -> p.subst (ctx1 ++ ctx) (ctx2 ++ ctx)
lift [<] f x = f x
lift (ctx :< ty) f Here = mon.var Here
lift (ctx :< ty) f (There x) = mon.ren (lift ctx f x) There


Strength : {Ty : Type} -> (f : SortedFamily {Ty} -> SortedFamily {Ty}) -> Type
Strength f = {p,x : SortedFamily {Ty}} -> (mon : PointedCoalgStruct p) =>
  (f (x ^ p)) -|> ((f x) ^ p)

SortedFunctor : {type : Type} -> Type
SortedFunctor {type} = SortedFamily {Ty=type} ->
                       SortedFamily {Ty=type}

SortedFunctorMap : {type : Type} -> SortedFunctor {type} -> Type
SortedFunctorMap {type} signature
  = {a,b : SortedFamily {Ty = type}} -> (a -|> b) ->
    signature a -|> signature b



parameters {Ty : Type} (signature : SortedFunctor {type = Ty})
                       (str : Strength {Ty} signature)
  record (.MonoidStruct) (x : SortedFamily {Ty}) where
    constructor MkSignatureMonoid
    mon : MonStruct x
    alg : signature x -|> x

  parameters (meta : SortedFamily {Ty})
    record MetaAlg (a : SortedFamily {Ty}) where
      constructor MkMetaAlg
      alg : signature a -|> a
      var : Var -|> a
      mvar : meta -|> (a ^ a)

    traverse : {p,a : SortedFamily {Ty}} ->
      (coalg : PointedCoalgStruct p) =>
      (alg : signature a -|> a) ->
      (phi : p -|> a) ->
      (chi : meta -|> (a ^ a)) -> MetaAlg (a ^ p)
    traverse {p,a} alg phi chi = MkMetaAlg
      { alg = \h,s => alg $ str h s
      , var = \v,s => phi (s v)
      , mvar = \m,e,s => chi m (\v => e v s)
      }

namespace TermDef
 mutual

    {- alas, non obviously strictly positive because we can't tell
     Idris that signature must be strictly positive.

     It will be, though, if we complete the termination project
    -}

  public export
  data Sub : {type : Type} -> {signature : SortedFunctor {type}} ->
       SortedFamily {Ty = type} -> Ctx {Ty = type} ->
       Ctx {Ty = type} -> Type where
      Lin :  Sub {type, signature} x [<] ctx
      (:<) : Sub {type, signature} x shape ctx ->
             signature.Term x ty ctx ->
             Sub {type,signature} x (shape :< ty) ctx

  public export
  data (.Term) : {type : Type} ->
       (signature : SortedFunctor {type}) ->
       SortedFamily {Ty = type} ->
       SortedFamily {Ty = type}
       where
    Op : {signature : SortedFunctor {type}} ->
         signature (signature.Term x) ty ctx ->
         signature.Term x ty ctx
    Va : Var ty ctx -> signature.Term x ty ctx
    Me : {ctx1, ctx2 : Ctx {Ty = type}} ->
         x ty ctx2 ->
         Sub (signature.Term {type} x)
             ctx2 ctx1 ->
         signature.Term {type} x ty ctx1

parameters {type : Type} {signature : SortedFunctor {type}}
  MetaContext : Type
  MetaContext = SnocList (Ctx {Ty=type}, type)

  (.metaEnv) : SortedFamily {Ty=type} -> MetaContext ->
               Family {Ty=type}
  x.metaEnv [<]            ctx = ()
  x.metaEnv (mctx :< meta) ctx =
    (x.metaEnv mctx ctx, (x <<< (fst meta)) (snd meta) ctx)

parameters {type : Type} {signature : SortedFunctor {type}}
           {auto signatureMap : SortedFunctorMap signature}
           {auto str : Strength {Ty = type} signature}
  parameters {x : SortedFamily {Ty = type}}
             (a : SortedFamily {Ty = type})
             {auto metalg : MetaAlg {Ty = type} signature str x a}
    (.envSem) : {ctx : Ctx} -> {mctx : MetaContext {signature}} ->
                (signature.Term x).metaEnv mctx ctx ->
                                 a.metaEnv mctx ctx
    (.subSem) : Sub (signature.Term x) ctx1 ctx2  ->
      a.subst ctx1 ctx2
    (.sem) : signature.Term x -|> a

    (.envSem) {mctx = [<]         } menv = ()
    (.envSem) {mctx = mctx :< meta} (menv,v) =
      ( (.envSem) menv
      , (.sem) v
      )

    (.sem) (Op args) = MetaAlg.alg _ _ _ metalg
                     $ signatureMap {b = a} (.sem) args
    (.sem) (Va x   ) = MetaAlg.var _ _ _ metalg x
    (.sem) {ctx = ctx1''} (Me  m env) = MetaAlg.mvar _ _ _ metalg m $ ((.subSem) env)


data (+) : {type : Type} -> (signature1, signature2 : SortedFunctor {type}) ->
  SortedFunctor {type} where
  Lft  :  {signature1, signature2 : SortedFunctor {type}} ->
    (op : sig1 x ty ctx) -> (sig1 + sig2) x ty ctx
  Rgt :  {signature1, signature2 : SortedFunctor {type}} ->
    (op : sig2 x ty ctx) -> (sig1 + sig2) x ty ctx


sum : {type : Type} -> (signatures : List $ (String, SortedFunctor {type})) ->
  SortedFunctor {type}
(sum signatures) x ty ctx = Any (\(name,sig) => sig x ty ctx) signatures

prod : {type : Type} -> (signatures : List $ SortedFunctor {type}) ->
  SortedFunctor {type}
(prod signatures) x ty ctx = All (\sig => sig x ty ctx) signatures

bind : {type : Type} -> (tys : Ctx {Ty = type}) ->  SortedFunctor {type}
bind tys = (<<< tys)

infixr 3 -:>

data TypeSTLC = B | (-:>) TypeSTLC TypeSTLC

data STLC : SortedFunctor {type = TypeSTLC} where
  App : (f : a (ty1 -:> ty2) ctx) -> (x : a ty1 ctx) -> STLC a ty2 ctx
  Lam : (body : a ty2 (ctx :< ty1)) ->
        STLC a (ty1 -:> ty2) ctx

foo : STLC .Term Var (B -:> (B -:> B) -:> B) [<]
foo = Op (Lam (Op (Lam (Op (App (Va Here) (Op (App (Va Here) (Va (There Here)))))))))
