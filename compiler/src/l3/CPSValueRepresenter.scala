package l3

import l3.{HighCPSTreeModule as H}
import l3.{LowCPSTreeModule as L}

import l3.{L3Primitive as L3}
import l3.{CPSValuePrimitive as CPS}
import l3.{CPSTestPrimitive as CPST}
import CL3Literal._

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree = {
    transform(tree) // transform is for trees , rewrite is for atoms
  }

  private def transform(tree: H.Tree): L.Tree = {
    tree match {
      // Continuations
      case H.LetC(cs, e) =>
        L.LetC(
          cs.map(c => L.Cnt(c.name, c.args, transform(c.body))),
          transform(e)
        )
      case H.AppC(c, as) =>
        L.AppC(c, as.map(rewrite))

      // Functions, wrong transformation
      case H.LetF(fs, e) =>
        L.LetF(
          fs.map(f => L.Fun(f.name, f.retC, f.args, transform(f.body))),
          transform(e)
        )
      case H.AppF(f, retC, as) =>
        L.AppF(rewrite(f), retC, as.map(rewrite))

      // Integers
      case H.LetP(n, L3.IntAdd, Seq(x, y), body) =>
        tempLetP(CPS.XOr, Seq(rewrite(x), 1)) { x1 =>
          L.LetP(n, CPS.Add, Seq(x1, rewrite(y)), apply(body))
        }
      case H.LetP(n, L3.IntSub, Seq(x, y), body) =>
        tempLetP(CPS.Sub, Seq(rewrite(x), rewrite(y))) { x1 =>
          L.LetP(n, CPS.Or, Seq(x1, 1), apply(body))
        }
      case H.LetP(n, L3.IntMul, Seq(x, y), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { b =>
          tempLetP(CPS.Sub, Seq(rewrite(x), 1)) { a =>
            tempLetP(CPS.Mul, Seq(a, b)) { t =>
              L.LetP(n, CPS.Add, Seq(t, 1), apply(body))
            }
          }
        }
      case H.LetP(n, L3.IntDiv, Seq(x, y), body) =>
        tempLetP(CPS.Sub, Seq(rewrite(x), 1)) { a =>
          tempLetP(CPS.Sub, Seq(rewrite(y), 1)) { b =>
            tempLetP(CPS.Div, Seq(a, b)) { c =>
              tempLetP(CPS.ShiftLeft, Seq(c, 1)) { d =>
                L.LetP(n, CPS.Add, Seq(d, 1), apply(body))
              }
            }
          }
        }

      case H.LetP(n, L3.IntMod, Seq(x, y), body) =>
        unboxInt(rewrite(x)) { c =>
          unboxInt(rewrite(y)) { d =>
            tempLetP(CPS.Mod, Seq(c, d)) { e =>
              boxInt(e, n) { f =>
                apply(body)
              }
            }
          }
        }

      // Bitwise operations
      case H.LetP(n, L3.IntShiftLeft, Seq(x, y), body) =>
        unboxInt(rewrite(y)) { y1 =>
          tempLetP(CPS.Sub, Seq(rewrite(x), 1)) { x1 =>
            tempLetP(CPS.ShiftLeft, Seq(x1, y1)) { t =>
              L.LetP(n, CPS.Add, Seq(t, 1), apply(body))
            }
          }
        }

      case H.LetP(n, L3.IntShiftRight, Seq(x, y), body) =>
        unboxInt(rewrite(y)) { y1 =>
          unboxInt(rewrite(x)) { x1 =>
            tempLetP(CPS.ShiftRight, Seq(x1, y1)) { t =>
              boxInt(t, n) { n =>
                apply(body)
              }
            }
          }
        }

      case H.LetP(n, L3.IntBitwiseAnd, Seq(x, y), body) =>
        L.LetP(n, CPS.And, Seq(rewrite(x), rewrite(y)), apply(body))

      case H.LetP(n, L3.IntBitwiseOr, Seq(x, y), body) =>
        L.LetP(n, CPS.Or, Seq(rewrite(x), rewrite(y)), apply(body))

      case H.LetP(n, L3.IntBitwiseXOr, Seq(x, y), body) =>
        tempLetP(CPS.XOr, Seq(rewrite(x), rewrite(y))) { t =>
          L.LetP(n, CPS.Add, Seq(t, 1), apply(body))
        }

      // Byte operations
      case H.LetP(n, L3.ByteRead, Seq(), body) =>
        tempLetP(CPS.ByteRead, Seq()) { t1 =>
          boxInt(t1, n) { _ => apply(body) }
        }

      case H.LetP(n, L3.ByteWrite, Seq(x), body) =>
        unboxInt(rewrite(x)) { x1 =>
          L.LetP(n, CPS.ByteWrite, Seq(x1), apply(body))
        }

      // Block operations
      case H.LetP(n, L3.BlockAlloc, Seq(x, y), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(x), 1)) { t1 =>
          tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { t2 =>
            L.LetP(n, CPS.BlockAlloc, Seq(t1, t2), apply(body))
          }
        }

      case H.LetP(n, L3.BlockTag, Seq(x), body) =>
        tempLetP(CPS.BlockTag, Seq(rewrite(x))) { t1 =>
          boxInt(t1, n) { _ => apply(body) }
        }

      case H.LetP(n, L3.BlockLength, Seq(x), body) =>
        tempLetP(CPS.BlockLength, Seq(rewrite(x))) { t1 =>
          boxInt(t1, n) { _ => apply(body) }
        }

      case H.LetP(n, L3.BlockGet, Seq(x, y), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { t1 =>
          L.LetP(n, CPS.BlockGet, Seq(rewrite(x), t1), apply(body))
        }

      case H.LetP(n, L3.BlockSet, Seq(x, y, z), body) =>
        tempLetP(CPS.ShiftRight, Seq(rewrite(y), 1)) { t1 =>
          L.LetP(n, CPS.BlockSet, Seq(rewrite(x), t1, rewrite(z)), apply(body))
        }

      // Conversions
      case H.LetP(n, L3.IntToChar, Seq(x), body) => {
        tempLetP(CPS.ShiftLeft, Seq(rewrite(x), 2)) { t1 =>
          L.LetP(n, CPS.Add, Seq(t1, 2), apply(body))
        }
      }

      case H.LetP(n, L3.CharToInt, Seq(x), body) => {
        L.LetP(n, CPS.ShiftRight, Seq(rewrite(x), 2), apply(body))
      }

      // Id
      case H.LetP(n, L3.Id, Seq(x), body) =>
        L.LetP(n, CPS.Id, Seq(rewrite(x)), apply(body))

      // Test primitive
      case H.If(L3.IntP, Seq(x), e1, e2) => {
        tempLetP(CPS.And, Seq(rewrite(x), 1)) { t1 =>
          L.If(CPST.Eq, Seq(t1, 1), e1, e2)
        }
      }

      case H.If(L3.CharP, Seq(x), e1, e2) => {
        tempLetP(CPS.And, Seq(rewrite(x), 7)) { t1 =>
          L.If(CPST.Eq, Seq(t1, 6), e1, e2)
        }
      }

      case H.If(L3.BoolP, Seq(x), e1, e2) => {
        tempLetP(CPS.And, Seq(rewrite(x), 15)) { t1 =>
          L.If(CPST.Eq, Seq(t1, 10), e1, e2)
        }
      }

      case H.If(L3.UnitP, Seq(x), e1, e2) => {
        tempLetP(CPS.And, Seq(rewrite(x), 15)) { t1 =>
          L.If(CPST.Eq, Seq(t1, 2), e1, e2)
        }
      }

      case H.If(L3.IntLt, Seq(x, y), e1, e2) => {
        L.If(CPST.Lt, Seq(rewrite(x), rewrite(y)), e1, e2)
      }
      case H.If(L3.IntLe, Seq(x, y), e1, e2) => {
        L.If(CPST.Le, Seq(rewrite(x), rewrite(y)), e1, e2)
      }
      case H.If(L3.Eq, Seq(x, y), e1, e2) => {
        L.If(CPST.Eq, Seq(rewrite(x), rewrite(y)), e1, e2)
      }

      case H.If(L3.BlockP, Seq(x), e1, e2) => {
        tempLetP(CPS.And, Seq(rewrite(x), 3)) { t1 =>
          L.If(CPST.Eq, Seq(t1, 0), e1, e2)
        }
      }

      case H.Halt(x) => unboxInt(rewrite(x)) { x1 => L.Halt(x1) }
      case _         => throw new Exception("Not implemented yet")

    }
  }

  private def boxInt(v: L.Name, n: L.Name)(body: L.Name => L.Tree): L.Tree = {
    tempLetP(CPS.ShiftLeft, Seq(v, 1)) { t =>
      L.LetP(n, CPS.Add, Seq(t, 1), body(v))
    }
  }

  private def unboxInt(x: L.Atom)(body: L.Name => L.Tree): L.Tree = {
    tempLetP(CPS.ShiftRight, Seq(x, 1)) { x2 =>
      body(x2)
    }
  }

  private def rewrite(a: H.Atom): L.Atom = {
    // Atom = Name | Literal
    a match {
      // case n: H.Name => n
      case n: H.Name => n

      // case l: H.Literal => l
      case IntLit(v)         => (v.toInt << 1) | 1
      case CharLit(c)        => (c.toInt << 3) | 6 // 0b110
      case BooleanLit(true)  => 26 // 0b11010
      case BooleanLit(false) => 10 // 0b01011
      case UnitLit           => 2 // 0b10
    }
  }

  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Atom])(
      body: L.Name => L.Tree
  ): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetP(tempSym, p, args, body(tempSym))
  }

}
