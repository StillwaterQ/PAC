# PAC: Physics-Aware Compilation for Parallel Quantum Circuit Execution on Neutral Atom Arrays
PAC (Physics-Aware Compilation) is a quantum compilation framework designed specifically for neutral atom quantum computers. It tackles the efficiency challenges of this promising architecture by balancing compilation efficiency with hardware flexibility, enabling scalable and high-performance quantum program execution.

## Features
1. Physics-Aware Hardware Partitioning
Leverages AOD/SLM trap properties and qubit mobility constraints to partition hardware effectively.

2. Parallel Quantum Circuit Division
Uses an improved Kernighan–Lin algorithm to divide circuits into parallelizable regions with high fidelity.

3. High Performance & Scalability
Achieves up to 78.5× speedup on 16×16 arrays and compiles 64×64 arrays in under 300 seconds.

## Project Structure & Usage
This project is implemented with Python 3.9. Please make sure to use the provided requirements.txt to replicate the environment.
```bash
conda create -n pac-env python=3.9
conda activate pac-env
pip install -r requirements.txt
```
## Directory Overview
```bash
pac/
├── solve_.py         # Core quantum compiler and scheduling logic
├── KL_algo.py        # Improved KL algorithm for quantum circuit partitioning
├── settings.py       # Experiment and hardware configuration settings
├── requirements.txt  # Python dependencies (pip format)
``` 

## Citation
If you use PAC in your work, please cite: [PAC]()
