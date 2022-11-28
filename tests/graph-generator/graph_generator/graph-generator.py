import argparse
import shutil
from itertools import combinations
from pathlib import Path

import networkx as nx
import pandas as pd
import requests
from sklearn import preprocessing
from tqdm.auto import tqdm

Path(f"./downloads/").mkdir(parents=True, exist_ok=True)

URI = "https://datasets.imdbws.com/"
FILES = ["title.basics.tsv.gz", "title.principals.tsv.gz", "name.basics.tsv.gz"]
FILEPATH_BASICS = Path(f"./downloads/{FILES[0]}")
FILEPATH_CAST = Path(f"./downloads/{FILES[1]}")
FILEPATH_NAME = Path(f"./downloads/{FILES[2]}")


def clean_basics(chunks, filter):
    df = pd.DataFrame()
    for chunk in chunks:
        chunk.startYear = chunk.startYear.apply(pd.to_numeric, errors="coerce")
        chunk = chunk.dropna()
        df = pd.concat([df, chunk.query(f"{filter}")], ignore_index=True)
    return df


def clean_cast(chunks):
    df = pd.DataFrame()
    for chunk in chunks:
        chunk.ordering = chunk.ordering.apply(pd.to_numeric, errors="coerce")
        chunk = chunk.dropna()
        df = pd.concat(
            [df, chunk.query("category == 'actor' | category == 'actress'")],
            ignore_index=True,
        )
    return df


def clean_name(chunks):
    df = pd.DataFrame()
    for chunk in chunks:
        chunk = chunk.dropna()
        df = pd.concat(
            [df, chunk],
            ignore_index=True,
        )
    return df


def download_data():
    for file in FILES:
        path = Path(f"./downloads/{file}")
        if not path.exists():
            print(f"Downloading {file}:")
            # make an HTTP request within a context manager
            with requests.get(f"{URI}{file}", stream=True) as r:
                # check header to get content length, in bytes
                total_length = int(r.headers.get("Content-Length"))

                # implement progress bar via tqdm
                with tqdm.wrapattr(r.raw, "read", total=total_length, desc="") as raw:
                    with open(path, "wb") as output:
                        shutil.copyfileobj(raw, output)


def read_data(query):
    print("Reading data")
    if (
        Path.exists(FILEPATH_BASICS)
        and Path.exists(FILEPATH_CAST)
        and Path.exists(FILEPATH_NAME)
    ):
        # read raw data
        chunks_basics = pd.read_csv(
            FILEPATH_BASICS,
            sep="\t",
            chunksize=pow(2, 16),
            usecols=["tconst", "originalTitle", "startYear", "titleType"],
        )
        chunks_cast = pd.read_csv(
            FILEPATH_CAST,
            sep="\t",
            chunksize=pow(2, 16),
            usecols=["tconst", "ordering", "nconst", "category"],
        )
        chunks_name = pd.read_csv(
            FILEPATH_NAME,
            sep="\t",
            chunksize=pow(2, 16),
            usecols=["nconst", "primaryName"],
        )

        # clean data
        df_basics = clean_basics(
            chunks_basics,
            f"{query} & titleType == 'movie'",  # command line parameter
        )
        df_cast = clean_cast(chunks_cast)
        df_name = clean_name(chunks_name)

        # merge and process
        df = pd.merge(df_basics, df_cast, on="tconst")
        df = pd.merge(df, df_name, on="nconst")

        le = preprocessing.LabelEncoder()
        le.fit(df.primaryName)
        df["label"] = le.transform(df.primaryName)

        df = df[
            [
                "originalTitle",
                "tconst",
                "nconst",
                "label",
                "primaryName",
                "startYear",
            ]
        ]

        df = df.set_index(["tconst", "nconst"])
        df = df.sort_index()
        return df


def create_graph(df):
    print("Building graph")
    G = nx.Graph()

    for film in df.groupby(level=0):
        edges = combinations(film[1].label.values, 2)
        G.add_edges_from(edges)
    return G


def write_graph(file, G):
    print("Writing graph")
    FILEPATH_RESULT = Path(f"./{file}")
    with open(FILEPATH_RESULT, "w") as writer:
        writer.write(f"p edge {nx.number_of_nodes(G)} {nx.number_of_edges(G)}\n")
        for e in G.edges:
            writer.write(f"e {e[0]} {e[1]}\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("query", help="Filter movies by year")
    parser.add_argument("file", help="Output filename")
    args = parser.parse_args()

    download_data()
    df = read_data(args.query)

    G = create_graph(df)
    write_graph(args.file, G)


if __name__ == "__main__":
    main()
