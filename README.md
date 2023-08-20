# Introduction
This is the code to use GPT-4 to generate action language BC and ASP code for solving a variety of domains.

## Installation
```
conda create --name gpt-r -c conda-forge python=3.11
conda activate gpt-r
conda install -c conda-forge openai
```

## Preparation
Include your OpenAI API key in line 2 of `api_keys.py`. API access to GPT-4 is required on your account.

## How to run

To run, use the command:
```
python main.py --o <OUTPUT FILE>
```
where <OUTPUT FILE> is the name of the file where the results will be writtent o.

To change the prompts, in `main.py` the prompts should be overwritten.
To change the domain description, query description, or semiformal hint, change the strings <domain>_desc, <domain>_query, and <domain>_semiformal_hint in `domains.py`.

Currently only lifting, shooting, hanoi, and the switches domain are used.
