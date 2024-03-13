package l3

import l3.{CL3Literal => CL3Lit}
import l3.{HighCPSTreeModule => H}
import l3.{L3Primitive => L3Prim}
import l3.{SymbolicCL3TreeModule => S}

/**
 * A translator from CL₃ to CPS.
 */


 

/**
  * TODO : refractor name generation
  * TODO : refractor some variable namings
  * TODO : rename context curry to transform curry maybe ? add reverse args
  * 
  */


object CL3ToCPSTranslator extends (S.Tree => H.Tree) {


  
  def apply(tree: S.Tree): H.Tree =
    transform(tree)(_ => H.Halt(CL3Lit.IntLit(L3Int(0))))

  // Maybe change name to curryTransform , and use foldLeft?
  def curryContext(trees: Seq[S.Tree], accContext: Seq[H.Atom])(ctx: Seq[H.Atom] => H.Tree): H.Tree =
    trees match {
      case Seq() => ctx(accContext)
      case Seq(e, es @ _*) => 
        transform(e)(a => curryContext(es,accContext :+ a)(ctx))
    }
  
  private def transform(tree : S.Tree)(ctx: H.Atom => H.Tree): H.Tree = {
    nonTail(tree)(ctx)
  }


  private def nonTail(tree : S.Tree)(ctx: H.Atom => H.Tree): H.Tree = {
    given Position = tree.pos

    //define here, literals need implicit position
    val l3true = S.Lit(CL3Lit.BooleanLit(true))
    val l3false = S.Lit(CL3Lit.BooleanLit(false))
    val l3Id = L3Prim.Id
    val l3Eq = L3Prim.Eq

    tree match {
      case S.Lit(value) => 
        ctx(value)
      case S.Ident(name) =>  
        ctx(name)
      case S.Let(Seq(),e) => 
        nonTail(e)(ctx)
      case S.Let(Seq((n1, e1), niei @_*), e) =>
        nonTail(e1)(a1 => H.LetP(n1, l3Id, Seq(a1), nonTail(S.Let(niei, e))(ctx)))
      case S.LetRec(fs, e) =>
        val cps_fs = fs map (f => 
          val retC = Symbol.fresh("ret_c")
          H.Fun(f.name, retC, f.args, nonTail(f.body)(a => H.AppC(retC, Seq(a))))
      )
        H.LetF(cps_fs, nonTail(e)(ctx))

      case S.App(f, args) =>
        val retCntName = Symbol.fresh("ret_c")
        val retCntArgName = Symbol.fresh("v")
        val appF = (a: H.Atom, as: Seq[H.Atom]) => H.AppF(a, retCntName, as)
        val retCnt = H.Cnt(retCntName, Seq(retCntArgName), ctx(retCntArgName))

        val initCtx = (as : Seq[H.Atom]) => 
          H.LetC(Seq(retCnt), nonTail(f)(a => appF(a, as)))
      
        curryContext(args, Seq())(as => initCtx(as)) //Do we need to reverse the args?

      
      case S.If(S.Prim(p:L3TestPrimitive, args), e2, e3) =>
        val ifCntName = Symbol.fresh("if_c")
        val ifCntArgName = Symbol.fresh("r")
        val thenCntName = Symbol.fresh("then_c")
        val elseCntName = Symbol.fresh("else_c")

        val ifCnt = H.Cnt(ifCntName, Seq(ifCntArgName), ctx(ifCntArgName))
        val thenCnt = H.Cnt(thenCntName, Seq(), nonTail(e2)(a2 => H.AppC(ifCntName, Seq(a2))))
        val elseCnt = H.Cnt(elseCntName, Seq(), nonTail(e3)(a3 => H.AppC(ifCntName, Seq(a3))))

        val letCBody = curryContext(args, Seq())(as => H.If(p, as, thenCntName, elseCntName))
        H.LetC(Seq(ifCnt, thenCnt, elseCnt), letCBody)
       
      case S.If(e1, e2, e3) =>
        nonTail(
          S.If(
            S.Prim(l3Eq, Seq(e1, l3false)), e3, e2)
          )
          (ctx)

      case tprim @ S.Prim(p:L3TestPrimitive , ei) =>
        nonTail(S.If(tprim,l3true,l3false))(ctx)
      
      case S.Prim(p:L3ValuePrimitive, args) =>
        val primName = Symbol.fresh("value_p")
        val initCtx = (as: Seq[H.Atom]) => H.LetP(primName, p, as, ctx(primName))
        curryContext(args, Seq())(as => initCtx(as))

      case S.Halt(arg) =>
        nonTail(arg)(H.Halt(_))
      
      case _ => throw new Exception("Non Tail : Not implemented !")
    }
  }

  def tail(tree: S.Tree, c: Symbol): H.Tree = {
    given Position = tree.pos

    val l3true = S.Lit(CL3Lit.BooleanLit(true))
    val l3false = S.Lit(CL3Lit.BooleanLit(false))
    val l3Id = L3Prim.Id

    tree match {
      case S.Lit(value) => H.AppC(c, Seq(value))
      case S.Ident(name) => H.AppC(c, Seq(name))
      case S.Let(Seq(), e) => tail(e, c)
      case S.Let(Seq((n1, e1), niei @_*), e) =>
        nonTail(e1)(a1 => H.LetP(n1, l3Id, Seq(a1), tail(S.Let(niei, e), c)))

      case S.LetRec(fs, e) =>
        val cps_fs = fs map (f => 
          val retC = Symbol.fresh("ret_c")
          H.Fun(f.name, retC, f.args, tail(f.body, retC))
        )
        H.LetF(cps_fs, tail(e, c))

      case S.If(e1,e2,e3) =>
        val thenCntName = Symbol.fresh("then_c")
        val elseCntName = Symbol.fresh("else_c")
        val thenCnt = H.Cnt(thenCntName, Seq(), tail(e2, c))
        val elseCnt = H.Cnt(elseCntName, Seq(), tail(e3, c))

        H.LetC(Seq(thenCnt),
          H.LetC(Seq(elseCnt),cond(e1,thenCntName,elseCntName))
        )
      case S.App(f, args) =>
        curryContext(args, Seq())(as => nonTail(f)(a => H.AppF(a, c, as)))
      
      case S.Prim(p:L3TestPrimitive, args) =>
        tail(S.If(S.Prim(p,args),l3true,l3false),c)
      
      case S.Prim(p:L3ValuePrimitive, args) =>
        val primName = Symbol.fresh("value_p")
        val initCtx = (as: Seq[H.Atom]) => H.LetP(primName, p, as, H.AppC(c, Seq(primName)))
        curryContext(args, Seq())(as => initCtx(as))
      
      case S.Halt(arg) => nonTail(arg)(H.Halt(_))
      case _ => throw new Exception("Tail : Not implemented !")
    }


  }

  def cond(tree: S.Tree, cThen:Symbol, cElse: Symbol): H.Tree = {
    given Position = tree.pos

    val l3true = S.Lit(CL3Lit.BooleanLit(true))
    val l3false = S.Lit(CL3Lit.BooleanLit(false))
    val l3Id = L3Prim.Id
    val l3Eq = L3Prim.Eq

    tree match {
      case id @ S.Ident(_) => cond(S.Prim(l3Eq, Seq(id, l3true)), cThen, cElse)
      case S.Lit(b @ CL3Lit.BooleanLit(_)) => H.AppC(if (b == l3true) cThen else cElse, Seq())
      case S.Lit(_) => H.AppC(cThen, Seq())
      case S.If(e1, e2 @ S.Lit(CL3Lit.BooleanLit(_)), e3 @ S.Lit(CL3Lit.BooleanLit(_))) =>
        cond(e1, if (e2 == l3true) cThen else cElse, if (e3 == l3true) cThen else cElse)
      case S.If(e1, e2, e3 @ S.Lit(CL3Lit.BooleanLit(_))) =>
        val acName = Symbol.fresh("ac")
        val (ctn,cen) = if (e3 == l3false) (cThen,cElse) else (cElse,cThen)
        val cnt = H.Cnt(acName, Seq(), cond(e2,ctn,cen))
        H.LetC(Seq(cnt),cond(e1,acName, cElse))
      case S.If(e1, e2 @ S.Lit(CL3Lit.BooleanLit(_)), e3) =>
        cond(S.If(e1,e3,e2),cThen,cElse)
      case S.Let(Seq(),body) => cond(body,cThen,cElse)
      case S.Let(Seq((n1, e1), niei @_*), e) =>
        nonTail(e1)(a1 => 
            H.LetP(n1,l3Id, Seq(a1), cond(S.Let(niei,e),cThen,cElse))
        )
      case S.Prim(p:L3TestPrimitive, args) =>
        curryContext(args, Seq())(as => H.If(p, as, cThen, cElse))
      
      case t => nonTail(t)(a => H.If(l3Eq, Seq(a, CL3Lit.BooleanLit(false)), cElse, cThen))
      case _ => throw new Exception("Cond : Not implemented !")
  }
}

}