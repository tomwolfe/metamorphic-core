FROM python:3.11-slim AS builder

WORKDIR /app
ENV PYTHONPATH=/app:/app/src

# System dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    build-essential \
    netcat-openbsd \
    && rm -rf /var/lib/apt/lists/*

# Install dependencies
COPY requirements/base.txt requirements/dev.txt ./
# Ensure pip is upgraded before installing requirements
RUN pip install --user --no-cache-dir --upgrade pip && \
    pip install --user --no-cache-dir -r base.txt -r dev.txt && \
    python -m spacy download en_core_web_sm

# Runtime image
FROM python:3.11-slim
WORKDIR /app
ENV PYTHONPATH=/app:/app/src
# --- CORRECTED PATH ---
# Add the location where user-installed packages' executables reside
ENV PATH="/root/.local/bin:${PATH}"

# Copy built python dependencies from the builder stage's user install location
COPY --from=builder /root/.local /root/.local

# Application code
COPY . .

EXPOSE 5000