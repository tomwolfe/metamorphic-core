"""
This module serves as the command-line interface (CLI) entry point for the Metamorphic Software Genesis Ecosystem. It provides basic argument parsing and placeholder functionality for future expansion.
"""

import argparse
import os


def _validate_roadmap_path(value):
    if not os.path.exists(value):
        raise argparse.ArgumentTypeError(f"Roadmap file {value} does not exist")
    return value


def _validate_output_dir(value):
    if not os.path.exists(value):
        raise argparse.ArgumentTypeError(f"Output directory {value} does not exist")
    if not os.path.isdir(value):
        raise argparse.ArgumentTypeError(f"{value} is not a directory")
    return value


def cli_entry_point():
    """
    Main entry point function for the CLI.

    Sets up the argument parser, handles version checks, and provides placeholder execution logic.
    """
    parser = argparse.ArgumentParser(
        description="Metamorphic Software Genesis Ecosystem CLI"
    )

    # Add version argument to display the current version and exit
    parser.add_argument(
        "--version",
        action="version",
        version="Metamorphic CLI v0.1.0-alpha",
        help="Show the version number and exit",
    )

    # Add roadmap argument with validation
    parser.add_argument(
        "--roadmap",
        type=_validate_roadmap_path,
        default="ROADMAP.json",
        help="Path to the roadmap JSON file.",
    )

    # Add output directory argument with validation
    parser.add_argument(
        "--output-dir",
        type=_validate_output_dir,
        default="./output",
        help="Path to the output directory.",
    )

    args = parser.parse_args()

    # Print parsed arguments for verification
    print(f"Using roadmap: {args.roadmap}")
    print(f"Using output directory: {args.output_dir}")


if __name__ == "__main__":
    cli_entry_point()