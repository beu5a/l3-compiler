package l3

import l3.{SymbolicCL3TreeModule => S}
import l3.{HighCPSTreeModule => H}

object CL3ToCPSTranslator extends (S.Tree => H.Tree) {

  val l3true = S.Lit(BooleanLit(true))
  val l3false = S.Lit(BooleanLit(false))
  
  def apply(tree: S.Tree): H.Tree =
    transform(tree)(_ => H.Halt(IntLit(L3Int(0))))
  
  def curryContext(trees: Seq[S.Tree], accContext: Seq[H.Atom])(ctx: Seq[H.Atom] => H.Tree): H.Tree =
    trees match {
      case Seq() => ctx(accContext)
      case Seq(e, es @ _*) => 
        transform(e)(a => curryContext(es,accContext :+ a)(ctx))
    }



  private def transform(tree : S.Tree)(ctx: H.Atom => H.Tree): H.Tree = {
    given Position = tree.pos

    tree match {
      case S.Lit(value) => 
        ctx(value)
      case S.Ident(name) =>  
        ctx(name)
      case S.Let(Seq(),e) => 
        transform(e)(ctx)
      case S.Let(Seq((n1, e1), niei @_*), e) =>
        transform(e1)(a1 => H.LetP(n1, L3Id, Seq(a1), transform(S.Let(niei, e))(ctx)))
      case S.LetRec(fs, e) =>
        val cps_fs = fs map {
          val retC = H.Name.fresh("ret_c")
          H.Fun(_.name, retC, _.args, transform(_.body)(a => H.AppC(retC, Seq(a))))
        }
        H.LetF(cps_fs, transform(e)(ctx))
      case S.App(f, args) =>
        
        val retCntName = H.Name.fresh("ret_c")
        val retCntArgName = H.Name.fresh("v")
        val appF = (as: Seq[Atom]) => H.AppF(f, retCntName, as)

        val initCtx = (as : Seq[H.Atom]) => {
          val retCnt = H.Cnt(retCntName, Seq(retCntArgName), ctx(retCntArgName))
          H.LetC(Seq(retCnt), appF(as))
        }
        curryContext(args, Seq())(as => initCtx(as)) //Do we need to reverse the args?
       
      case S.If(e1, e2, e3) =>
        transform(
          S.If(S.Prim(L3Eq, Seq(e1, l3false)), e3, e2)
          )
          (ctx)
      case p @ S.Prim(p:L3TestPrimitive , ei) =>
        transform(
          S.If(p,l3true,l3false)
        )
        (ctx)
      
      case _ @ S.Prim(p:L3ValuePrimitive, args) =>

        



    }
  }
    


}
