# BealsTriples
 Exploration of Beal's triples of form A^i + B^j = C^k

Further information on this interesting mathematical conjecture may be found at:
www.bealconjecture.com/
www.math.unt.edu/~mauldin/beal.html

So, why this search?  This repository includes code to search the smallest possible triples in order.  It searched about 800 trillion combinations of B^j and C^k up to the first 100 million C^k values.

Those values are filtered to remove duplicates, only the form with the smallest base value is kept and other ways to arrive at the same value are removed, leaving the first 100 million.

And the results are published in a list of just over 16,000 triples which satisfy the equality.  It is hoped that those good mathematicians interested in the problem might explore those numbers to look for inspiration about what properties may explain the conjecture.  The list is in a comma-separated format which you can easily import into a spreadsheet or other program.

As an example of some simple manipulations you can do with these, you could sort the results in rising value of GCD(A B C).  Another fascinating sort is to add a secondary sort on the log10_A_i column.

You can do other things like looking for sequential solutions which have neighboring GCD values.  There are quite a few of these.

Finally, I added a separate, simple program which scans for the nearest misses - when there is no exact solution for a specific B^j, what was the A^i, C^j combination which came closest to equality?  The fun thing here is that about 60% of these near-miss results are mutually prime - even though not a single one of the exact results is mutually prime.  This is a simple way to show how amazing the GCD property of the exact triples really is.

Have fun, and don't go too far down the rabbit-hole spending time on this conjecture!
