#!/usr/bin/env python3

import pandas as pd

import argparse

parser = argparse.ArgumentParser()
parser.add_argument("results", help="results CSV (with header)")

args = parser.parse_args()

df = pd.read_csv(args.results)
print(df.groupby(["system", "bench"]).agg(['median', 'min', 'max']))
