# src/cli/main.py
"""
This module serves as the command-line interface (CLI) entry point for the Metamorphic Software Genesis Ecosystem.
It provides argument parsing with validation for roadmap files and output directories.
"""

import argparse
import os


def _validate_roadmap_path(value):
    """Validate the provided roadmap file path.

    Args:
        value (str): Path to the roadmap file

    Returns:
        str: Validated absolute path if validation passes

    Raises:
        argparse.ArgumentTypeError: If path doesn't exist or isn't a file
    """
    if not os.path.exists(value):
        raise argparse.ArgumentTypeError(f"Roadmap file {value} does not exist")
    if not os.path.isfile(value):
        raise argparse.ArgumentTypeError(f"{value} is not a valid file")
    return os.path.abspath(value)


def _validate_output_dir(value):
    """Validate the provided output directory path.

    Args:
        value (str): Path to the output directory

    Returns:
        str: Validated absolute path if validation passes

    Raises:
        argparse.ArgumentTypeError: If path doesn't exist or isn't a directory
    """
    if not os.path.exists(value):
        raise argparse.ArgumentTypeError(f"Output directory {value} does not exist")
    if not os.path.isdir(value):
        raise argparse.ArgumentTypeError(f"{value} is not a directory")
    return os.path.abspath(value)


def cli_entry_point():
    """
    Main entry point function for the CLI.

    Sets up the argument parser with roadmap and output directory arguments,
    handles validation, and executes the main logic.
    """
    parser = argparse.ArgumentParser(
        description="Metamorphic Software Genesis Ecosystem CLI",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    # Version argument
    parser.add_argument(
        "--version",
        action="version",
        version="Metamorphic CLI v0.1.0-alpha",
        help="Show the version number and exit",
    )

    # Roadmap file argument
    parser.add_argument(
        "--roadmap",
        type=_validate_roadmap_path,
        default="ROADMAP.json",
        help="Path to the roadmap JSON file",
    )

    # Output directory argument
    parser.add_argument(
        "--output-dir",
        type=_validate_output_dir,
        default="./output",
        help="Path to the output directory",
    )

    args = parser.parse_args()

    # Display validated paths for verification
    print(f"Using roadmap: {args.roadmap}")
    print(f"Using output directory: {args.output_dir}")


if __name__ == "__main__":
    cli_entry_point()