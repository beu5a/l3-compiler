package l3

import l3.{HighCPSTreeModule as H}
import l3.{LowCPSTreeModule as L}

import l3.{L3Primitve as L3}
import l3.{CPSValuePrimitive as CPS}
import l3.{CPSTestPrimitive as CPST}
import CL3Literal._


object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree = {
    tree match {
      case H.LetP(n,L3.IntAdd, Seq(x, y), body) => 
        val x1 = Symbol.fresh("t")
        tempLetP(CPS.XOr, Seq(rewrite(x), 1)) { x1 => 
          L.LetP(n, CPS.Add, Seq(x1,rewrite(y)), apply(body))
        }
    }
  }

  private def rewrite(a:H.Atom):L.Atom = {
    a match {
      case n: H.Name => n
      case Intlit(v) => (v.toInt  <<  1) | 1
    }
  }

  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Atom])(body: L.Name => L.Tree): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetP(tempSym, p, args, body(tempSym))
  }

}
