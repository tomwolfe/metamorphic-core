# src/api/server.py
from flask import Flask, jsonify, request
import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..')))
from src.api.routes.ethical_endpoints import ethical_bp
from src.api.routes.workflow_endpoints import workflow_bp  # Import workflow_bp
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
import logging
import redis
from src.core.llm_orchestration import LLMOrchestrator

startup_done = False

app = Flask(__name__)
# --- MODIFICATION START ---
# Configure Flask-Limiter to use Redis storage
# Use REDIS_URL environment variable, fall back to in-memory if not set (for local dev/testing without docker-compose)
REDIS_URL = os.getenv("REDIS_URL", "memory://")
limiter = Limiter(get_remote_address, app=app, storage_uri=REDIS_URL)
# --- MODIFICATION END ---


logging.basicConfig(level=logging.INFO)

llm_orchestrator = LLMOrchestrator()
app.llm_orchestrator = llm_orchestrator


@app.route('/generate', methods=['POST'])  # Direct route for /generate - Option 1
@limiter.limit("5/minute")
def generate_endpoint():
    prompt = request.get_json().get('prompt')
    return jsonify({"generated": "output-text"}), 200


@app.route('/genesis/test-endpoint')
def test_endpoint():
    return jsonify({"status": "test-route-working"}), 200


app.register_blueprint(ethical_bp, url_prefix='/genesis')
app.register_blueprint(workflow_bp, url_prefix='/genesis')  # Register workflow_bp


@app.before_request
def startup_debug():
    global startup_done
    if not startup_done:
        import socket
        hostname = socket.gethostname()
        ip = socket.gethostbyname(hostname)
        app.logger.info(f"Flask running on {ip}:5000")
        app.logger.info(f"Flask host binding to: 0.0.0.0:5000")
        try:
            # --- MODIFICATION START ---
            # Check Redis connection only if a Redis URL is configured
            if REDIS_URL.startswith("redis://"):
                # Parse the URL to get host and port
                from urllib.parse import urlparse
                parsed_url = urlparse(REDIS_URL)
                redis_host = parsed_url.hostname or 'localhost'
                redis_port = parsed_url.port or 6379

                redis_client = redis.Redis(host=redis_host, port=redis_port)
                response = redis_client.ping()
                if response:
                    app.logger.info("Redis connection successful")
                else:
                    app.logger.warning("Redis ping failed but connection might still be alive.")
            else:
                 app.logger.info("Using in-memory storage for Flask-Limiter (no Redis configured).")
            # --- MODIFICATION END ---
        except Exception as e:
            app.logger.error(f"Redis connection check failed: {str(e)}")
        app.logger.info("--- Environment Variables ---")
        keys_to_log = ['LLM_PROVIDER', 'GEMINI_API_KEY', 'YOUR_GITHUB_API_KEY',
                       'HUGGING_FACE_API_KEY', 'ZAP_API_KEY', 'REDIS_URL'] # Added REDIS_URL
        for key in keys_to_log:
            value = os.environ.get(key, 'NOT SET')
            # Avoid logging sensitive keys' values directly
            if key in ['GEMINI_API_KEY', 'YOUR_GITHUB_API_KEY', 'HUGGING_FACE_API_KEY', 'ZAP_API_KEY'] and value != 'NOT SET':
                 app.logger.info(f"{key}: {'********'}")
            else:
                 app.logger.info(f"{key}: {value}")
        app.logger.info("--- End Environment Variables ---")
        startup_done = True


if __name__ == '__main__':
    # The app.run() call is missing here, but this file is likely run via gunicorn or similar in production/docker.
    # For local testing, you might need app.run(debug=True, host='0.0.0.0', port=5000)
    app.run(debug=False, host='0.0.0.0') # Explicitly disable debug and bind to 0.0.0.0