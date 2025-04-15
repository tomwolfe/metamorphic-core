import logging
from pathlib import Path

logger = logging.getLogger(__name__)

def write_file(filepath, content, overwrite=False):
    """
    Write content to a file, handling exceptions and logging.

    Args:
        filepath (str): The path to the file to write to.
        content (str): The content to write to the file.
        overwrite (bool, optional): Whether to overwrite the file if it exists.
            Defaults to False.

    Returns:
        bool: True if the file was written successfully, False otherwise.
    """
    # Sanitize the file path to prevent path traversal
    sanitized_path = Path(filepath).resolve()

    # Check if the file exists and we shouldn't overwrite it
    if not overwrite and sanitized_path.exists():
        return False

    try:
        # Attempt to open the file in write mode ('w')
        with open(sanitized_path, 'w') as file:
            file.write(content)
    except (FileNotFoundError, PermissionError) as e:
        # Log the error and return False
        logger.error(f"Error writing to {sanitized_path}: {str(e)}")
        return False

    # Log success and return True
    logger.info(f"Successfully wrote to {sanitized_path}")
    return True