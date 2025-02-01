from flask import Flask, request, jsonify
from flask_limiter import Limiter
from src.core import ArchitectureGraph, QuantumCodeOptimizer
from google import genai
from src.utils.config import SecureConfig

app = Flask(__name__)
limiter = Limiter(app=app)
genai.configure(api_key=SecureConfig.get('GEMINI_API_KEY'))
llm = genai.GenerativeModel('gemini-pro')

@app.route('/generate', methods=['POST'])
@limiter.limit("5/minute")
def generate_endpoint():
    return jsonify({"status": "System operational"})

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
