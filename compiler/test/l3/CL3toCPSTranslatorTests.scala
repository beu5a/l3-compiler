package l3

import utest._

import SymbolicCL3TreeModule.Tree
import l3.{HighCPSTreeModule => H}
import l3.{SymbolicCL3TreeModule => S}
import l3.{CL3ToCPSTranslator => CL3ToCPS}
import l3.{CL3Literal => CL3Lit}
import l3.{L3Primitive => L3Prim}



trait  CL3toCPSTranslatorTests {

    val backEnd: S.Tree => H.Tree

    implicit val pos: l3.Position = l3.UnknownPosition

    val tests = Tests{
        test("CL3toCPSTranslator 1"){
            val tree = S.Lit(CL3Lit.IntLit(L3Int(0)))
            val expected = H.Halt(CL3Lit.IntLit(L3Int(0)))
            assert(CL3ToCPS(tree) == expected)
        }
        test("CL3toCPSTranslator Optimise LetRec"){
            // (letrec ((f (fun (g) (g)))) f)
            def idProvider = new Iterator[Int] {
                var i = 0
                def next() = { i += 1; i }
                def hasNext = true
            }

            val g = Symbol("g", idProvider.next())
            val f = Symbol("f", idProvider.next())
            val c = Symbol("c", idProvider.next())

            assert(true == true)
        }
    }
}

object CL3toCPSTranslatorTests1 extends TestSuite with CL3toCPSTranslatorTests {
    val backEnd = l3.L3Tester.backEnd3
}
