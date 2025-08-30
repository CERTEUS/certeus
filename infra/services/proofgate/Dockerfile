FROM python:3.11-slim
WORKDIR /app

# zależności minimalne pod stub
COPY requirements.txt /app/requirements.txt
RUN pip install --no-cache-dir -r /app/requirements.txt

# kod aplikacji
COPY . /app

EXPOSE 8081
CMD ["python","-m","uvicorn","services.proofgate.app:app","--host","0.0.0.0","--port","8081"]
