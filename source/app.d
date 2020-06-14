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

	static void insertion_sort(ref Interval[] a, int left, int right) {
		for (auto i = left + 1; i <= right; i++) {
			compexch(a[left], a[i]);
		}
		for (auto i = left + 2; i <= right; i++) {
			auto j = i;
			auto v = a[i];
			while (less(v, a[j - 1])) {
				a[j] = a[j - 1];
				j--;
			}
			a[j] = v;
		}
	}

	static void exch(ref Interval a, ref Interval b) {
		Interval tmp = a;
		a = b;
		b = tmp;
	}

	static bool less(ref Interval a, ref Interval b) {
		return a.start < b.start;
	}

	static void compexch(ref Interval a, ref Interval b) {
		if (less(b, a)) {
			exch(a, b);
		}
	}

	static auto partition(ref Interval[] a, size_t left, size_t right) {
		auto i = left - 1;
		auto j = right;
		auto v = a[right];

		while (true) {
			while (less(a[++i], v)) {
			}
			while (less(v, a[--j])) {
				if (j == left) {
					break;
				}
			}
			if (i >= j) {
				break;
			}
			exch(a[i], a[j]);
		}
		exch(a[i], a[right]);
		return i;
	}

	// left is leftmost index
	// right is rightmost index
	static void quicksort(ref Interval[] a, size_t left, size_t right) {
		immutable size_t min = 10;
		// Base case
		if (right - left < min) {
			// Do insertion sort instead
			insertion_sort(a, cast(int) left, cast(int) right);
			return;
		}

		exch(a[(left + right) / 2], a[right - 1]);
		compexch(a[left], a[right - 1]);
		compexch(a[left], a[right]);
		compexch(a[right - 1], a[right]);
		auto i = partition(a, left + 1, right - 1);
		quicksort(a, left, i - 1);
		quicksort(a, i + 1, right);
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
		alias lessThan = (x, y) => x.start < y.start;
		this.ivs.sort!(Interval.lessThan);
		// this.quicksort(ivs, 0, ivs.length - 1);
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
