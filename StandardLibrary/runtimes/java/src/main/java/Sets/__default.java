package Sets;

import dafny.DafnySequence;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.ArrayList;

public class __default {
  public static <T> dafny.DafnySequence<? extends dafny.DafnySequence<? extends T>>
      SetToOrderedSequence(
	 dafny.TypeDescriptor<T> td_T,
	 dafny.DafnySet<? extends dafny.DafnySequence<? extends T>> inputSet,
	 dafny.Function2<T, T, Boolean> less)
  {
      dafny.DafnySequence<? extends T>[] outputArray = new DafnySequence[inputSet.size()];
      outputArray = inputSet.Elements().toArray(outputArray);
      LexicographicComparer<T> cmp = new LexicographicComparer<T>(less);
      Arrays.sort(outputArray, cmp);
      return DafnySequence.fromRawArray(DafnySequence._typeDescriptor(td_T), outputArray);
  }

  public static <T> dafny.DafnySequence<? extends dafny.DafnySequence<? extends T>>
      SetToOrderedSequence2(
	 dafny.TypeDescriptor<T> _td_T,
	 dafny.DafnySet<? extends dafny.DafnySequence<? extends T>> s,
	 dafny.Function2<T, T, Boolean> less)
  {
      return SetToOrderedSequence(_td_T, s, less);
  }

  public static <T> dafny.DafnySequence<? extends T>
      SetToSequence(
	 dafny.TypeDescriptor<T> td_T,
	 dafny.DafnySet<? extends T> inputSet)
  {
      return DafnySequence.fromList(td_T, new ArrayList<T>(inputSet.Elements()));
  }

}


class LexicographicComparer <T> implements Comparator<dafny.DafnySequence<? extends T>> {
    private dafny.Function2<T, T, Boolean> less;
    public LexicographicComparer(dafny.Function2<T, T, Boolean> less) {
        this.less = less;
    }

    public int compare(dafny.DafnySequence<? extends T> x, dafny.DafnySequence<? extends T> y) {
        for (int i = 0; i < x.length() && i < y.length(); i++) {
            if (less.apply(x.select(i), y.select(i))) {
                return -1;
            }
            if (this.less.apply(y.select(i), x.select(i))) {
                return 1;
            }
        }
        // Reached the end of one array. Either they are equal, or the
        // one which is shorter should be considered "less than"
        return Integer.compare(x.length(), y.length());
    }
}
