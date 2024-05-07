using System;

namespace Lemon
{
  // Then we define any C# methods that Dafny may need:
  public class ConsoleIO
  {
    public static void WriteLine(Dafny.ISequence<Dafny.Rune> line) {
      Console.WriteLine(line.ToVerbatimString(false));
    }
  
    public static Dafny.ISequence<Dafny.Rune> ReadLine() {
      var line = Console.ReadLine();
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(line);
    }
  }
/*
  namespace CSharpUtils {
    public partial class StringUtils {
      public static Dafny.ISequence<Dafny.Rune> StringAsDafnyString(String s) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(s);
      }
      public static String DafnyStringAsString(Dafny.ISequence<Dafny.Rune> ds) {
        return ds.ToVerbatimString(false);
      }
    }

    public partial class ListUtils {
      public static B FoldR<A, B>(Func<A, B, B> f, B b0, List<A> lA) {
        for (int i = lA.Count - 1; i >= 0; i--) {
          b0 = f(lA[i], b0);
        }
        return b0;
      }
    }
  }
*/
  class Program {
    public static void Main(string[] args) {
      //Console.Out.NewLine = "\n";
      /*
      Console.WriteLine("# Step 1: Parse");
      var ast = parse(args[0]);
      Console.WriteLine($"cAST =\n  {ast}");

      Console.WriteLine("\n# Step 2: Compile (using Dafny)");
      var pp = SimpleCompiler.DafnyCompiler.CompileAndExport(ast);

      Console.WriteLine("\n# Step 3: Print (using C#)");
      pp.ForEach(s => Console.WriteLine($"  {s}"));
      */
    }
  }
}