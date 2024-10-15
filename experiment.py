#!/usr/bin/python3

import argparse
import subprocess
import numpy as np
from tqdm import tqdm
import matplotlib
matplotlib.use('Agg')  # Use the Agg backend for environments without a display
import matplotlib.pyplot as plt
from string import Template
import sys

def parse_arguments():
    parser = argparse.ArgumentParser(description='Benchmarking and Graphing Tool with Sequential Mode Support')
    parser.add_argument('--constant_param', required=True, help='Constant parameter for all runs')
    parser.add_argument('--version', action='append', required=True, help='Algorithm version (can be specified multiple times)')
    parser.add_argument('--scale', action='append', help='Scale parameter for 2D plots (can be specified multiple times)')
    parser.add_argument('--scale_x', action='append', help='Scale X parameter for 3D plots (can be specified multiple times)')
    parser.add_argument('--scale_y', action='append', help='Scale Y parameter for 3D plots (can be specified multiple times)')
    parser.add_argument('--seq', action='store_true', help='Activate sequential mode where the benchmark outputs a sequence of results')
    parser.add_argument('--num_runs', type=int, default=1, help='Number of times to repeat each benchmark')
    parser.add_argument('--output_file', default='benchmark_results.png', help='Output graph file name')
    parser.add_argument('--benchmark_cmd', required=True, help='Benchmark command template with placeholders')
    parser.add_argument('--x_label', help='Label for the X-axis')
    parser.add_argument('--y_label', help='Label for the Y-axis')
    parser.add_argument('--z_label', help='Label for the Z-axis in 3D plots')
    parser.add_argument('--title', default='Algorithm Performance Benchmark', help='Title of the graph')
    # Arguments for figure size and label rotation
    parser.add_argument('--fig_size', nargs=2, type=float, help='Figure size as width height in inches, e.g., --fig_size 12 6')
    parser.add_argument('--x_label_rotation', type=float, default=0, help='Rotation angle for X-axis labels in degrees')
    return parser.parse_args()

def run_benchmarks_2d(constant_param, versions, scales, num_runs, benchmark_cmd_template):
    results = {}
    total_iterations = len(versions) * len(scales) * num_runs

    # Initialize the progress bar
    progress_bar = tqdm(total=total_iterations, desc='Benchmarking', unit='run')

    # Create a Template object
    cmd_template = Template(benchmark_cmd_template)

    for version in versions:
        means = []
        std_devs = []
        for scale in scales:
            run_results = []
            for _ in range(num_runs):
                # Substitute parameters using Template
                benchmark_cmd = cmd_template.substitute(
                    constant_param=constant_param,
                    version=version,
                    scale=scale
                )
                try:
                    # Execute the benchmark command
                    output = subprocess.check_output(benchmark_cmd, shell=True)
                    # Decode and convert the output to a float
                    result = float(output.decode().strip())
                    run_results.append(result)
                except subprocess.CalledProcessError as e:
                    print(f'\nError executing command: {benchmark_cmd}')
                    print(e.output.decode())
                    run_results.append(np.nan)  # Append NaN for failed runs
                except ValueError:
                    print(f'\nInvalid output for command: {benchmark_cmd}')
                    run_results.append(np.nan)
                finally:
                    # Update the progress bar
                    progress_bar.update(1)
            # Compute mean and standard deviation, ignoring NaN values
            mean = np.nanmean(run_results)
            std_dev = np.nanstd(run_results)
            means.append(mean)
            std_devs.append(std_dev)
        results[version] = {'means': means, 'std_devs': std_devs}
    progress_bar.close()
    return results

def run_benchmarks_3d(constant_param, versions, scales_x, scales_y, num_runs, benchmark_cmd_template):
    results = {}
    total_iterations = len(versions) * len(scales_x) * len(scales_y) * num_runs

    # Initialize the progress bar
    progress_bar = tqdm(total=total_iterations, desc='Benchmarking', unit='run')

    # Create a Template object
    cmd_template = Template(benchmark_cmd_template)

    for version in versions:
        version_results = []
        for scale_x in scales_x:
            scale_x_results = []
            for scale_y in scales_y:
                run_results = []
                for _ in range(num_runs):
                    # Substitute parameters using Template
                    benchmark_cmd = cmd_template.substitute(
                        constant_param=constant_param,
                        version=version,
                        scale_x=scale_x,
                        scale_y=scale_y
                    )
                    try:
                        # Execute the benchmark command
                        output = subprocess.check_output(benchmark_cmd, shell=True)
                        # Decode and convert the output to a float
                        result = float(output.decode().strip())
                        run_results.append(result)
                    except subprocess.CalledProcessError as e:
                        print(f'\nError executing command: {benchmark_cmd}')
                        print(e.output.decode())
                        run_results.append(np.nan)  # Append NaN for failed runs
                    except ValueError:
                        print(f'\nInvalid output for command: {benchmark_cmd}')
                        run_results.append(np.nan)
                    finally:
                        # Update the progress bar
                        progress_bar.update(1)
                # Compute mean, ignoring NaN values
                mean = np.nanmean(run_results)
                scale_x_results.append(mean)
            version_results.append(scale_x_results)
        results[version] = np.array(version_results)
    progress_bar.close()
    return results

def run_benchmarks_seq(constant_param, versions, num_runs, benchmark_cmd_template):
    results = {}
    # Total iterations is versions * num_runs
    total_iterations = len(versions) * num_runs

    # Initialize the progress bar
    progress_bar = tqdm(total=total_iterations, desc='Benchmarking', unit='run')

    # Create a Template object
    cmd_template = Template(benchmark_cmd_template)

    for version in versions:
        all_scales = []
        all_results = []
        for _ in range(num_runs):
            # Substitute parameters using Template
            benchmark_cmd = cmd_template.substitute(
                constant_param=constant_param,
                version=version
            )
            try:
                # Execute the benchmark command
                output = subprocess.check_output(benchmark_cmd, shell=True)
                # Decode and split the output into lines
                lines = output.decode().strip().split('\n')
                print(benchmark_cmd + " -> " + str(lines))
                scales = []
                results_list = []
                for line in lines:
                    # Each line should have scale and result separated by whitespace
                    parts = line.strip().split()
                    if len(parts) != 2:
                        print(f'\nInvalid output line: "{line}"')
                        continue
                    scale_str, result_str = parts
                    try:
                        scale = float(scale_str)
                        result = float(result_str)
                        scales.append(scale)
                        results_list.append(result)
                    except ValueError:
                        print(f'\nInvalid scale or result in line: "{line}"')
                        continue
                all_scales.append(scales)
                all_results.append(results_list)
            except subprocess.CalledProcessError as e:
                print(f'\nError executing command: {benchmark_cmd}')
                print(e.output.decode())
                all_scales.append([])
                all_results.append([])
            finally:
                # Update the progress bar
                progress_bar.update(1)
        # Aggregate results
        # Since scales can be different for each run, we need to handle this carefully
        # We'll create a dictionary mapping scales to lists of results
        scale_results = {}
        for scales, results_list in zip(all_scales, all_results):
            for scale, result in zip(scales, results_list):
                if scale not in scale_results:
                    scale_results[scale] = []
                scale_results[scale].append(result)
        # Compute mean and std dev for each scale
        scales = list(scale_results.keys())
        scales.sort()  # Sort scales numerically
        means = []
        std_devs = []
        for scale in scales:
            result_list = scale_results[scale]
            mean = np.nanmean(result_list)
            std_dev = np.nanstd(result_list)
            means.append(mean)
            std_devs.append(std_dev)
        # Store results
        results[version] = {'scales': scales, 'means': means, 'std_devs': std_devs}
    progress_bar.close()
    return results

def plot_results_2d(scales, results, output_file, x_label, y_label, title, fig_size=None, x_label_rotation=0):
    # Convert scales to strings in case they are not numeric
    scales = [str(scale) for scale in scales]
    x_indices = np.arange(len(scales))

    # Create a new figure with specified size
    if fig_size:
        plt.figure(figsize=fig_size)
    else:
        plt.figure()

    for version, data in results.items():
        means = data['means']
        std_devs = data['std_devs']
        plt.errorbar(x_indices, means, yerr=std_devs, marker='o', capsize=5, label=version)
    plt.xlabel(x_label)
    plt.ylabel(y_label)
    plt.title(title)
    plt.legend()
    plt.grid(True)
    plt.xticks(x_indices, scales, rotation=x_label_rotation)  # Rotate X-axis labels
    plt.tight_layout()  # Adjust layout to prevent label cutoff
    plt.savefig(output_file)
    plt.close()  # Close the figure to free up memory

def plot_results_seq(results, output_file, x_label, y_label, title, fig_size=None, x_label_rotation=0):
    # Create a new figure with specified size
    if fig_size:
        plt.figure(figsize=fig_size)
    else:
        plt.figure()

    for version, data in results.items():
        scales = data['scales']  # Scales are numeric
        means = data['means']
        std_devs = data['std_devs']
        plt.errorbar(scales, means, yerr=std_devs, marker='o', capsize=5, label=version)
    plt.xlabel(x_label)
    plt.ylabel(y_label)
    plt.title(title)
    plt.legend()
    plt.grid(True)
    # Rotate X-axis labels if needed
    if x_label_rotation != 0:
        plt.xticks(rotation=x_label_rotation)
    plt.tight_layout()  # Adjust layout to prevent label cutoff
    plt.savefig(output_file)
    plt.close()  # Close the figure to free up memory

def plot_results_3d(scales_x, scales_y, results, output_file, x_label, y_label, z_label, title, fig_size=None, x_label_rotation=0, y_label_rotation=0):
    # Map scales to indices
    scales_x = [str(sx) for sx in scales_x]
    scales_y = [str(sy) for sy in scales_y]
    x_indices = np.arange(len(scales_x))
    y_indices = np.arange(len(scales_y))
    x_mesh, y_mesh = np.meshgrid(x_indices, y_indices, indexing='ij')

    # Create a new figure with specified size
    if fig_size:
        fig = plt.figure(figsize=fig_size)
    else:
        fig = plt.figure()

    ax = fig.add_subplot(111, projection='3d')

    # Define colormap
    colors = plt.cm.viridis(np.linspace(0, 1, len(results)))
    for idx, (version, data) in enumerate(results.items()):
        # data is a 2D array of means with shape (len(scales_x), len(scales_y))
        surf = ax.plot_surface(x_mesh, y_mesh, data, color=colors[idx], alpha=0.7)
    ax.set_xlabel(x_label)
    ax.set_ylabel(y_label)
    ax.set_zlabel(z_label)
    ax.set_title(title)

    # Set custom ticks for x and y axes
    ax.set_xticks(x_indices)
    ax.set_xticklabels(scales_x, rotation=x_label_rotation, ha='right')
    ax.set_yticks(y_indices)
    ax.set_yticklabels(scales_y, rotation=y_label_rotation, va='center')

    # Create custom legend
    from matplotlib.patches import Patch
    legend_elements = [Patch(facecolor=colors[idx], edgecolor='k', label=version) for idx, version in enumerate(results.keys())]
    ax.legend(handles=legend_elements)

    plt.tight_layout()
    plt.savefig(output_file)
    plt.close()

def main():
    args = parse_arguments()
    constant_param = args.constant_param
    versions = args.version
    num_runs = args.num_runs
    benchmark_cmd_template = args.benchmark_cmd

    if args.seq:
        # Sequential mode
        # Set default labels if not provided
        x_label = args.x_label if args.x_label else 'Scale Parameter'
        y_label = args.y_label if args.y_label else 'Benchmark Result'
        # Run benchmarks and plot
        results = run_benchmarks_seq(constant_param, versions, num_runs, benchmark_cmd_template)
        plot_results_seq(
            results, args.output_file, x_label, y_label, args.title,
            fig_size=args.fig_size,
            x_label_rotation=args.x_label_rotation
        )
    elif args.scale and not args.scale_x and not args.scale_y:
        # 2D plot
        scales = args.scale
        # Set default labels if not provided
        x_label = args.x_label if args.x_label else 'Scale Parameter'
        y_label = args.y_label if args.y_label else 'Benchmark Result'
        # Run benchmarks and plot
        results = run_benchmarks_2d(constant_param, versions, scales, num_runs, benchmark_cmd_template)
        plot_results_2d(
            scales, results, args.output_file, x_label, y_label, args.title,
            fig_size=args.fig_size,
            x_label_rotation=args.x_label_rotation
        )
    elif args.scale_x and args.scale_y and not args.scale:
        # 3D plot
        scales_x = args.scale_x
        scales_y = args.scale_y
        # Set default labels if not provided
        x_label = args.x_label if args.x_label else 'Scale X'
        y_label = args.y_label if args.y_label else 'Scale Y'
        z_label = args.z_label if args.z_label else 'Benchmark Result'
        # Run benchmarks and plot
        results = run_benchmarks_3d(constant_param, versions, scales_x, scales_y, num_runs, benchmark_cmd_template)
        plot_results_3d(
            scales_x, scales_y, results, args.output_file, x_label, y_label, z_label, args.title,
            fig_size=args.fig_size,
            x_label_rotation=args.x_label_rotation,
            y_label_rotation=0  # You can add an argument for Y-axis label rotation if needed
        )
    else:
        print("Invalid combination of options.")
        print("For sequential mode, use '--seq' without '--scale', '--scale_x', or '--scale_y'.")
        print("For 2D plots, provide '--scale'.")
        print("For 3D plots, provide both '--scale_x' and '--scale_y'.")
        sys.exit(1)

if __name__ == '__main__':
    main()
