package l3

import FlatCPSTreeModule as F
import LowCPSTreeModule as L

object CPSHoister extends (L.Tree => F.Program) {
  def apply(tree: L.Tree): F.Program =
    tree match
      case L.LetF(funs, body) => {
        val F.LetF(funs1, body1) = apply(body)
        def funToFun(f: L.Fun): (F.Fun, Seq[F.Fun]) = {
          val F.LetF(fsi, ei) = apply(f.body)
          (F.Fun(f.name, f.retC, f.args, ei), fsi)
        }
        val (f1, f2) = funs.map(funToFun).unzip
        F.LetF(f1 ++ f2.flatten ++ funs1, body1)
      }

      case L.LetC(cnts, body) => {
        val F.LetF(fs, e) = apply(body)
        def cntToCnt(c: L.Cnt): (F.Cnt, Seq[F.Fun]) = {
          val F.LetF(fsii, ei) = apply(c.body)
          (F.Cnt(c.name, c.args, ei), fsii)
        }
        val (cntsi, fsi) = cnts.map(cntToCnt).unzip
        F.LetF(fsi.flatten ++ fs, F.LetC(cntsi, e))
      }

      case L.LetP(name, prim, args, body) => {
        val F.LetF(funs1, body1) = apply(body)
        F.LetF(funs1, F.LetP(name, prim, args, body1))
      }

      case _ => F.LetF(Seq(), convert(tree))


  def convert(tree: L.Tree): F.Body = {
    tree match
      case L.AppC(cnt, args)              => F.AppC(cnt, args)
      case L.AppF(fun, retC, args)        => F.AppF(fun, retC, args)
      case L.Halt(arg)                    => F.Halt(arg)
      case L.If(cond, args, thenC, elseC) => F.If(cond, args, thenC, elseC)
      case _ => throw new Exception(s"unexpected tree: $tree") // LetF, LetC, LetP already handled by apply
  }
}
