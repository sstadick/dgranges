module source.app;

import std.getopt;
import std.array : appender;
import std.stdio;
import std.math : pow;
import std.algorithm : splitter, sort;
import std.range : take;
import std.typecons;
import std.string;
import std.conv;

class IITree(SType, DType) {

	Interval[] ivs;
	int max_level;

	struct StackCell {
		size_t x;
		int k; // level
		int w; //  0 if left child hasn't been processed, 1 if left has been processed

		this(int k, size_t x, int w) {
			this.k = k;
			this.x = x;
			this.w = w;
		}
	}

	// TODO: Skip the bits that have alraedy been sorted
	static void insertion_sort(ref Interval[] ivs) {
		for (auto i = 1; i < ivs.length; i++) {
			immutable auto key = ivs[i];
			auto j = i - 1;
			while (j >= 0 && key.start < ivs[j].start) {
				ivs[j + 1] = ivs[j];
				j--;
			}
			ivs[j + 1] = key;
		}
	}

	void radix_sort(ref Interval[] ivs) {
		if (ivs.length < 64 || SType.sizeof < 2) {
			insertion_sort(ivs);
		} else {
			rs_sort(ivs);
		}
	}

	// Get the ith radix of a. Radix is the number of bits to look at at once
	static auto digit(SType a, size_t i) {
		immutable auto radix = 16;
		return ((a >> (SType.sizeof * 8 - (i + 1) * radix)) & ((1 << radix) - 1));
	}

	static void exchange(ref Interval a, ref Interval b) {
		Interval tmp;
		tmp = a;
		a = b;
		b = tmp;
	}

	static void quicksortX(ref Interval[] ivs, int low, int high, size_t d) {
		if (high - low <= 64) {
			insertion_sort(ivs);
			return;
		}
		if ((high - low) <= 0) {
			return;
		}
		auto v = digit(ivs[high].start, d);
		auto i = low - 1;
		auto j = high;
		auto p = low - 1;
		auto q = high;

		while (i < j) {
			while (digit(ivs[++i].start, d) < v) {
				if (i == high)
					break;
			}
			while (v < digit(ivs[--j].start, d)) {
				if (j == low)
					break;
			}
			if (i > j)
				break;
			exchange(ivs[i], ivs[j]);
			if (digit(ivs[i].start, d) == v) {
				exchange(ivs[++p], ivs[i]);
			}
			if (v == digit(ivs[j].start, d)) {
				exchange(ivs[j], ivs[--q]);
			}
		}
		if (p == q) {
			// might be missing an exit point here
			quicksortX(ivs, low, high, d + 1);
			return;
		}
		if (digit(ivs[i].start, d) < v)
			i++;
		for (auto k = low; k <= p; k++) {
			exchange(ivs[k], ivs[j--]);
		}
		for (auto k = high; k >= q; k--)
			exchange(ivs[k], ivs[i++]);
		quicksortX(ivs, low, j, d);
		if ((i == high) && (digit(ivs[i].start, d) == v))
			i++;
		// might be missing exit here
		quicksortX(ivs, j + 1, i - 1, d + 1);
		quicksortX(ivs, i, high, d);
	}

	static void rs_sort(ref Interval[] ivs) {
		auto count = 0;
		immutable auto R = 8; // sort 16 bits at a time, so assume we are more than 16 bit keys
		immutable auto K = 1 << R; //pow(2, R);
		immutable auto WORDSIZE = SType.sizeof * 8;

		size_t[K] buckets; //= new size_t[K];
		size_t[K] positions; // = new size_t[K];
		while (count < (SType.sizeof * 8) / R) {
			// zero out buckets
			for (auto i = 0; i < K; i++) {
				buckets[i] = 0;
				positions[i] = 0;
			}

			// Find how many items's keys are in each bucket
			foreach (iv; ivs) {
				buckets[((iv.start >> (WORDSIZE - ((count) + 1) * R)) & (K - 1))] += 1;
			}

			// Find the number of elements less than or equal to i at each position
			for (auto i = 1; i < K; i++) {
				buckets[i] += buckets[i - 1];
			}
			// Copy buckets into positions so that buckets can be modified
			positions[0 .. $] = buckets[0 .. $];
			auto i = 0;
			while (i < ivs.length) {
				// Looking to place item
				auto key = ((ivs[i].start >> (WORDSIZE - ((count) + 1) * R)) & (K - 1));
				bool placed = (key == 0 || (positions[key - 1] <= i && i < positions[key]));
				if (placed) {
					i += 1;
				} else {
					auto tmp = ivs[i];
					ivs[i] = ivs[buckets[key] - 1];
					ivs[buckets[key] - 1] = tmp;
					buckets[key] -= 1;
				}
			}
			count += 1;
		}

	}

	struct Interval {
		SType start;
		SType stop;
		SType max;
		DType data;
		static bool lessThan(const Interval self, const Interval other) {
			return self.start < other.start;
		}
	}

	void index() {
		// alias lessThan = (x, y) => x.start < y.start;
		// this.ivs.sort!(Interval.lessThan);
		// this.rs_sort(ivs);
		this.quicksortX(ivs, 0, cast(int) ivs.length - 1, 0);
		auto last = 0; // last is the max value at node last_i
		auto last_i = 1; // last_i points to the rightmost node in the tree
		for (auto i = 0; i < this.ivs.length; i += 2) {
			last_i = i;
			last = this.ivs[i].stop;
			this.ivs[i].max = last;
		}
		auto k = 1;
		for (; 1 << k <= this.ivs.length; ++k) { // process internal nodes in the bottom up-order
			auto x = 1 << (k - 1);
			auto i0 = (x << 1) - 1;
			immutable auto step = x << 2;
			for (auto i = i0; i < this.ivs.length; i += step) { // traverse all nodes at level k
				immutable auto el = this.ivs[i - x].max; // max value of the left child
				immutable auto er = i + x < this.ivs.length ? this.ivs[i + x].max : last; // max value of the right child
				auto e = this.ivs[i].stop;
				e = e > el ? e : el;
				e = e > er ? e : er;
				this.ivs[i].max = e; // set the max value fo node i
			}
			last_i = (last_i >> k & 1) ? last_i - x : last_i + x;
			if (last_i < this.ivs.length && this.ivs[last_i].max > last)
				last = this.ivs[last_i].max;
		}
		this.max_level = k - 1; // Set max level for IITree
	}

	void add(const SType start, const SType stop, const DType data) {
		this.ivs ~= Interval(start, stop, 0, data);
	}

	void overlap(SType start, SType stop, void delegate(Interval) blck) {
		auto t = 0;
		StackCell[64] stack;
		stack[t++] = StackCell(this.max_level, (1 << this.max_level) - 1, 0); // push the root; this is a top down traversal
		while (t) { // the following guarantess that numer in out[] are always sorted
			StackCell z = stack[--t];
			if (z.k <= 3) { // we ar in a smal subtree; traverse every node in this subtree
				auto i0 = z.x >> z.k << z.k;
				auto i1 = i0 + (1 << (z.k + 1)) - 1;
				if (i1 >= this.ivs.length)
					i1 = this.ivs.length;
				for (auto i = i0; i < i1 && this.ivs[i].start < stop; ++i) {
					if (start < this.ivs[i].stop) { // if overlap, append to out[]
						blck(this.ivs[i]);
					}
				}
			} else if (z.w == 0) { // if left child not processed
				size_t y = z.x - (1 << (z.k - 1)); // the left child of z.x; NB: y may be out of range (i.e. y >= ivs.length)
				stack[t++] = StackCell(z.k, z.x, 1); // re-add node z.x but mark the left child having been processed
				if (y >= this.ivs.length || this.ivs[y].max > start) { // push the left child if y is out of range or may overlap query
					stack[t++] = StackCell(z.k - 1, y, 0);
				}
			} else if (z.x < this.ivs.length && this.ivs[z.x].start < stop) { // need to push the right child
				if (start < this.ivs[z.x].stop) {
					blck(this.ivs[z.x]); // test if z.x overlaps the query;
				}
				stack[t++] = StackCell(z.k - 1, z.x + (1 << (z.k - 1)), 0); // push the right child
			}
		}
	}
}

pragma(inline, true);
ref auto next(T)(ref T iter) {
	auto tmp = iter.front;
	iter.popFront;
	return tmp;
}

void main(string[] args) {
	string fileA, fileB;
	auto helpInfo = getopt(args, config.required, "fileA|a", &fileA,
			config.required, "fileB|b", &fileB);
	if (helpInfo.helpWanted) {
		defaultGetoptPrinter("Calculate coverage.", helpInfo.options);
	}
	alias Itree = IITree!(int, bool);
	alias Iv = Itree.Interval;
	Itree[string] bed;
	auto inFile = File(fileA);
	foreach (line; inFile.byLine()) {
		auto iter = line.splitter('\t');
		auto chr = iter.next;
		auto start = iter.next;
		auto stop = iter.next;
		if (!(chr in bed)) {
			bed[chr.to!string] = new Itree();
		}
		bed[chr].add(start.to!int, stop.to!int, true);
	}

	// Index the trees
	foreach (tree; bed.values)
		tree.index;
	inFile = File(fileB);
	foreach (line; inFile.byLine()) {
		auto iter = line.splitter('\t');
		auto chr = iter.next;
		auto start = iter.next;
		auto stop = iter.next;
		if (!(chr in bed)) {
			core.stdc.stdio.printf("%.*s\t%.*s\t%.*s\t0\t0\n",
					cast(int) chr.length, chr.ptr, cast(int) start.length,
					start.ptr, cast(int) stop.length, stop.ptr);
		} else {
			auto st0 = start.to!int;
			auto en0 = stop.to!int;
			auto cov_st = 0;
			auto cov_en = 0;
			auto cov = 0;
			auto n = 0;
			void callback(Iv x) {
				n += 1;
				const auto st1 = x.start > st0 ? x.start : st0;
				const auto en1 = x.stop < en0 ? x.stop : en0;
				if (st1 > cov_en) {
					cov += cov_en - cov_st;
					cov_st = st1;
					cov_en = en1;
				} else {
					if (cov_en < en1)
						cov_en = en1;
				}
			}

			bed[chr].overlap(st0, en0, &callback);
			cov += cov_en - cov_st;
			core.stdc.stdio.printf("%.*s\t%d\t%d\t%d\t%d\n",
					cast(int) chr.length, chr.ptr, st0, en0, n, cov);
		}

	}
}

// Figure out what the output order should be
unittest {
	write("Testing indexing: ");
	alias Itree = IITree!(int, bool);
	alias Iv = Itree.Interval;
	Iv[] ivs = [Iv(5, 8, 0, true), Iv(0, 4, 0, true), Iv(3, 10, 0, true)];
	Itree tree = new Itree();
	foreach (iv; ivs) {
		tree.add(iv.start, iv.stop, iv.data);
	}
	tree.index();
	assert(tree.ivs == [
			Iv(0, 4, 4, true), Iv(3, 10, 10, true), Iv(5, 8, 8, true)
			]);
	writeln("Passed");
}

unittest {
	write("Testing radix sort: ");
	alias Itree = IITree!(int, bool);
	alias Iv = Itree.Interval;
	Iv[] ivs = [Iv(5, 8, 0, true), Iv(0, 4, 0, true), Iv(3, 10, 0, true)];
	Itree.rs_sort(ivs);
	assert(ivs == [Iv(0, 4, 0, true), Iv(3, 10, 0, true), Iv(5, 8, 0, true)]);
	writeln("Passed");
}

unittest {
	write("Testing radix sort: ");
	alias Itree = IITree!(int, bool);
	alias Iv = Itree.Interval;
	Iv[] ivs = [Iv(5, 8, 0, true), Iv(0, 4, 0, true), Iv(3, 10, 0, true)];
	Itree.quicksortX(ivs, 0, cast(int) ivs.length - 1, 0);
	assert(ivs == [Iv(0, 4, 0, true), Iv(3, 10, 0, true), Iv(5, 8, 0, true)]);
	writeln("Passed");
}

// Sanity check
unittest {
	write("Testing find: ");
	alias Itree = IITree!(int, bool);
	alias Iv = Itree.Interval;
	Iv[] ivs = [Iv(5, 8, 0, true), Iv(0, 4, 0, true), Iv(3, 10, 0, true)];
	Itree tree = new Itree();
	foreach (iv; ivs) {
		tree.add(iv.start, iv.stop, iv.data);
	}
	tree.index();
	auto found = 0;
	void incFound(Iv iv) {
		found++;
	}

	tree.overlap(6, 10, &incFound);
	assert(found == 2);
	writeln("Passed");
}
