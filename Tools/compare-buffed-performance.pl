#!/usr/bin/env perl
# Compare two already-built buffed-benchmark executables with identical inputs.
# Usage: compare-buffed-performance.pl BASELINE CURRENT [count=10000] [samples=9] [pc=100]
# PERF_CPU pins both binaries using taskset; PERF_CSV saves raw measured samples.
# Optional PERF_MAX_RATIO fails on regressions above that ratio, excluding phases
# shorter than PERF_MIN_MS (default 1ms). All timings are still reported.
# Build both binaries with the same toolchain/LTO settings. Do not build concurrently
# with this script. Two warmups per binary/case are discarded; run order alternates.
use strict;
use warnings;
use Cwd qw(abs_path);
use List::Util qw(sum);

my ($baseline, $current, $count, $samples, $pc) = @ARGV;
die "Usage: $0 BASELINE CURRENT [count] [samples] [pc]\n"
  unless defined($baseline) && defined($current) && @ARGV <= 5;
$count //= 10000;
$samples //= 9;
$pc //= 100;
die "Expected positive count, at least 3 samples, and pc in 0..100\n"
  unless $count =~ /^\d+$/ && $count > 0 && $samples =~ /^\d+$/ && $samples >= 3
    && $pc =~ /^\d+$/ && $pc <= 100;
my %binary = (baseline => $baseline, current => $current);
for my $version (keys %binary) {
  my $path = abs_path($binary{$version});
  die "Not an executable: $binary{$version}\n" unless defined($path) && -f $path && -x $path;
  $binary{$version} = $path;
}
my $max_ratio = $ENV{PERF_MAX_RATIO};
my $min_ms = $ENV{PERF_MIN_MS} // 1;
for my $value ($max_ratio, $min_ms) {
  die "Timing thresholds must be nonnegative numbers\n"
    if defined($value) && $value !~ /^\d+(?:\.\d+)?$/;
}
my @prefix = defined($ENV{PERF_CPU}) ? ('taskset', '-c', $ENV{PERF_CPU}) : ();
my @benches = qw(
  add-fold-forwards add-zero-forwards add-zero-reuse-forwards mul-two-forwards
  add-fold-forwards-sparse add-zero-forwards-sparse mul-two-forwards-sparse
  add-zero-reuse-first add-zero-lots-of-reuse-first
);
my $csv;
if (defined $ENV{PERF_CSV}) {
  open $csv, '>', $ENV{PERF_CSV} or die "$ENV{PERF_CSV}: $!\n";
  print $csv "benchmark,count,pc,round,version,create_s,rewrite_s\n";
}
my %data;
for my $round (-2 .. $samples - 1) {
  my @ordered = $round % 2 ? reverse(@benches) : @benches;
  for my $bench (@ordered) {
    my @versions = $round % 2 ? qw(current baseline) : qw(baseline current);
    for my $version (@versions) {
      open my $pipe, '-|', @prefix, $binary{$version}, $bench, $count, $pc
        or die "Cannot start $version/$bench: $!\n";
      my $output = do { local $/; <$pipe> };
      close $pipe or die "Failed $version/$bench (status $?)\n";
      my ($create) = $output =~ /^create time \(s\): ([\d.eE+-]+)$/m;
      my ($rewrite) = $output =~ /^rewrite time \(s\): ([\d.eE+-]+)$/m;
      # The executable can return success even when the Option computation failed.
      die "Missing timings for $version/$bench:\n$output"
        unless defined($create) && defined($rewrite);
      next if $round < 0;
      print $csv "$bench,$count,$pc,$round,$version,$create,$rewrite\n" if defined $csv;
      push @{$data{$bench}{$version}{create}}, 0 + $create;
      push @{$data{$bench}{$version}{rewrite}}, 0 + $rewrite;
    }
  }
  print STDERR $round < 0 ? "Warmup complete\n" : "Sample " . ($round + 1) . "/$samples complete\n";
}
close $csv or die "Cannot finish CSV: $!\n" if defined $csv;

sub median {
  my @values = sort { $a <=> $b } @_;
  my $n = @values;
  return $n % 2 ? $values[int($n / 2)] : ($values[$n / 2 - 1] + $values[$n / 2]) / 2;
}
sub cv {
  my $mean = sum(@_) / scalar(@_);
  return 0 if $mean == 0;
  return sqrt(sum(map { ($_ - $mean) ** 2 } @_) / (scalar(@_) - 1)) / $mean * 100;
}
my $failed = 0;
print "benchmark\tphase\tbaseline_ms\tcurrent_ms\tratio\tbaseline_cv_pct\tcurrent_cv_pct\n";
for my $bench (@benches) {
  for my $phase (qw(create rewrite)) {
    my @before = @{$data{$bench}{baseline}{$phase}};
    my @after = @{$data{$bench}{current}{$phase}};
    my $b = median(@before);
    my $c = median(@after);
    my $ratio = $b > 0 ? sprintf('%.3f', $c / $b) : 'n/a';
    printf "%s\t%s\t%.3f\t%.3f\t%s\t%.2f\t%.2f\n",
      $bench, $phase, $b * 1000, $c * 1000, $ratio, cv(@before), cv(@after);
    if (defined($max_ratio) && $b > 0 && $b * 1000 >= $min_ms && $c / $b > $max_ratio) {
      warn "Regression: $bench/$phase ($ratio > $max_ratio)\n";
      $failed = 1;
    }
  }
}
exit $failed;
