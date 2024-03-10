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
        transform(e)(ctx)
      case S.Let(Seq((n1, e1), niei @_*), e) =>
        transform(e1)(a1 => H.LetP(n1, l3Id, Seq(a1), transform(S.Let(niei, e))(ctx)))
      case S.LetRec(fs, e) =>
        val cps_fs = fs map (f => 
          val retC = Symbol.fresh("ret_c")
          H.Fun(f.name, retC, f.args, transform(f.body)(a => H.AppC(retC, Seq(a))))
      )
        H.LetF(cps_fs, transform(e)(ctx))

      case S.App(f, args) =>
        val retCntName = Symbol.fresh("ret_c")
        val retCntArgName = Symbol.fresh("v")
        val appF = (a: H.Atom, as: Seq[H.Atom]) => H.AppF(a, retCntName, as)
        val retCnt = H.Cnt(retCntName, Seq(retCntArgName), ctx(retCntArgName))

        val initCtx = (as : Seq[H.Atom]) => 
          H.LetC(Seq(retCnt), transform(f)(a => appF(a, as)))
      
        curryContext(args, Seq())(as => initCtx(as)) //Do we need to reverse the args?

      
      case S.If(S.Prim(p:L3TestPrimitive, args), e2, e3) =>
        val ifCntName = Symbol.fresh("if_c")
        val ifCntArgName = Symbol.fresh("r")
        val thenCntName = Symbol.fresh("then_c")
        val elseCntName = Symbol.fresh("else_c")

        val ifCnt = H.Cnt(ifCntName, Seq(ifCntArgName), ctx(ifCntArgName))
        val thenCnt = H.Cnt(thenCntName, Seq(), transform(e2)(a2 => H.AppC(ifCntName, Seq(a2))))
        val elseCnt = H.Cnt(elseCntName, Seq(), transform(e3)(a3 => H.AppC(ifCntName, Seq(a3))))

        val letCBody = curryContext(args, Seq())(as => H.If(p, as, thenCntName, elseCntName))
        H.LetC(Seq(ifCnt, thenCnt, elseCnt), letCBody)
       
      case S.If(e1, e2, e3) =>
        transform(
          S.If(
            S.Prim(l3Eq, Seq(e1, l3false)), e3, e2)
          )
          (ctx)

      case tprim @ S.Prim(p:L3TestPrimitive , ei) =>
        transform(S.If(tprim,l3true,l3false))(ctx)
      
      case S.Prim(p:L3ValuePrimitive, args) =>
        val primName = Symbol.fresh("value_p")
        val initCtx = (as: Seq[H.Atom]) => H.LetP(primName, p, as, ctx(primName))
        curryContext(args, Seq())(as => initCtx(as))

      case S.Halt(arg) =>
        transform(arg)(H.Halt(_))
      
      case _ => sys.error("Not implemented yet")
        



    }
  }
    


}
