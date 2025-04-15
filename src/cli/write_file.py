import logging
import os
from pathlib import Path

logger = logging.getLogger(__name__)


def file_exists(filepath: str) -> bool:
    """
    Check if a file exists at the given filepath after sanitizing the path.

    Args:
        filepath (str): The path to check.

    Returns:
        bool: True if the file exists, False otherwise.
    """
    sanitized_path = Path(filepath).resolve()
    return os.path.isfile(sanitized_path)


def write_file(
    filepath: str, content: str, overwrite: bool = False
) -> bool:
    """
    Write content to a file, handling exceptions and logging.

    Args:
        filepath (str): The path to the file to write to.
        content (str): The content to write to the file.
        overwrite (bool, optional): Whether to overwrite the file if it exists.
            Defaults to False.

    Returns:
        bool: True if the file was written successfully, False otherwise.

    Raises:
        FileExistsError: If the file exists and overwrite is False.
    """
    sanitized_path = Path(filepath).resolve()

    # Check if the file exists and we shouldn't overwrite it
    if not overwrite and file_exists(filepath):
        raise FileExistsError(
            f"File {sanitized_path} already exists and overwrite is False"
        )

    try:
        # Attempt to open the file in write mode ('w')
        with open(sanitized_path, "w") as file:
            file.write(content)
        logger.info(f"Successfully wrote to {sanitized_path}")
        return True
    except (FileNotFoundError, PermissionError) as e:
        # Log the error and return False
        logger.error(f"Error writing to {sanitized_path}: {str(e)}")
        return False