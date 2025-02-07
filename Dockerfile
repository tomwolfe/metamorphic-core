FROM python:3.11-slim as builder

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
RUN pip install --user --no-cache-dir --upgrade pip && \
    pip install --user --no-cache-dir -r base.txt -r dev.txt

# Runtime image
FROM python:3.11-slim
WORKDIR /app
ENV PYTHONPATH=/app:/app/src
ENV PATH="/app/.local/bin:${PATH}"

# Copy built python dependencies
COPY --from=builder /root/.local /root/.local

# Application code
COPY . .

EXPOSE 5000
CMD ["python", "src/api/server.py"]
