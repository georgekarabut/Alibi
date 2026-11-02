(() => {
  'use strict';
  const box = document.querySelector('.hero-game');
  if (!box) return;
  // Картинки: итоговый вид, слой «до» (волосы + борода) и карта локонов (R+G = id, B = маска волос)
  const SRC = {
    after: 'assets/images/game-after.webp',
    locks: 'assets/images/game-locks.webp',
    map: 'assets/images/game-locks-map.png'
  };
  const cv = box.querySelector('canvas'),
    ctx = cv.getContext('2d');
  const bar = box.querySelector('.hero-game-progress span');
  const done = box.querySelector('.hero-game-done');
  const again = box.querySelector('.hero-game-again');
  const reduce = matchMedia('(prefers-reduced-motion: reduce)');
  const load = src => new Promise((ok, fail) => {
    const i = new Image();
    // С другого домена картинку можно читать на холсте только с CORS
    i.crossOrigin = 'anonymous';
    i.onload = () => ok(i);
    i.onerror = fail;
    i.src = src;
  });
  const canvas = (w, h) => {
    const c = document.createElement('canvas');
    c.width = w;
    c.height = h;
    return c;
  };
  // Карту локонов читаем из байтов PNG, а не с холста: Safari на iOS 26 подмешивает шум в getImageData,
  // и номера локонов в R+G рассыпаются на тысячи ложных
  async function readMap(src) {
    if (!window.DecompressionStream) {
      const img = await load(src),
        w = img.naturalWidth,
        h = img.naturalHeight,
        k = canvas(w, h).getContext('2d');
      k.drawImage(img, 0, 0);
      return { w, h, data: k.getImageData(0, 0, w, h).data };
    }
    const res = await fetch(src);
    if (!res.ok) throw Error(src);
    const buf = new Uint8Array(await res.arrayBuffer()),
      dv = new DataView(buf.buffer),
      parts = [];
    let w = 0, h = 0;
    for (let o = 8; o + 8 <= buf.length;) {
      const len = dv.getUint32(o),
        type = String.fromCharCode(...buf.subarray(o + 4, o + 8));
      if (type === 'IHDR') {
        w = dv.getUint32(o + 8);
        h = dv.getUint32(o + 12);
        // Поддерживаем только то, что лежит в репозитории: 8 бит, RGBA, без чересстрочности
        if (buf[o + 16] !== 8 || buf[o + 17] !== 6 || buf[o + 20]) throw Error('PNG format');
      } else if (type === 'IDAT') parts.push(buf.subarray(o + 8, o + 8 + len));
      else if (type === 'IEND') break;
      o += len + 12;
    }
    const stream = new Blob(parts).stream().pipeThrough(new DecompressionStream('deflate'));
    const raw = new Uint8Array(await new Response(stream).arrayBuffer()),
      row = w * 4,
      data = new Uint8Array(w * h * 4);
    // Снимаем построчные фильтры PNG (None, Sub, Up, Average, Paeth)
    for (let y = 0; y < h; y++) {
      const f = raw[y * (row + 1)],
        s = y * (row + 1) + 1,
        t = y * row;
      for (let i = 0; i < row; i++) {
        const a = i >= 4 ? data[t + i - 4] : 0,
          b = y ? data[t + i - row] : 0,
          c = i >= 4 && y ? data[t + i - row - 4] : 0;
        let v = raw[s + i];
        if (f === 1) v += a;
        else if (f === 2) v += b;
        else if (f === 3) v += (a + b) >> 1;
        else if (f === 4) {
          const p = a + b - c,
            pa = Math.abs(p - a),
            pb = Math.abs(p - b),
            pc = Math.abs(p - c);
          v += pa <= pb && pa <= pc ? a : pb <= pc ? b : c;
        }
        data[t + i] = v;
      }
    }
    return { w, h, data };
  }
  let after, locksImg, layer, lctx, IW, IH, MW, MH, labels, R, bg = '#151e38',
    total = 1,
    cutArea = 0,
    layerA = 1,
    fadeTo = 1;
  let scale = 1,
    ox = 0,
    oy = 0,
    dpr = 1,
    running = false,
    finishing = false;
  const pieces = [],
    byId = new Map(),
    falling = [],
    pointers = new Map();
  // Режем слой «до» на локоны по карте: для каждого id — картинка локона и жёсткая маска для вырезания
  function build(locksImg, map) {
    MW = map.w;
    MH = map.h;
    const md = map.data;
    labels = new Uint16Array(MW * MH);
    for (let i = 0; i < labels.length; i++)
      if (md[i * 4 + 3] > 128) labels[i] = md[i * 4] + md[i * 4 + 1] * 256;
    const kx = MW / IW,
      ky = MH / IH,
      mi = (x, y) => Math.min(MH - 1, y * ky | 0) * MW + Math.min(MW - 1, x * kx | 0),
      lab = (x, y) => labels[mi(x, y)];
    const boxes = new Map();
    for (let y = 0; y < IH; y++)
      for (let x = 0; x < IW; x++) {
        const id = lab(x, y);
        if (!id) continue;
        let b = boxes.get(id);
        if (!b) boxes.set(id, b = {
          x0: x,
          y0: y,
          x1: x,
          y1: y,
          n: 0
        });
        if (x < b.x0) b.x0 = x;
        if (x > b.x1) b.x1 = x;
        if (y > b.y1) b.y1 = y;
        b.n++;
      }
    for (const [id, b] of boxes) {
      const w = b.x1 - b.x0 + 1,
        h = b.y1 - b.y0 + 1,
        c = canvas(w, h),
        k = c.getContext('2d'),
        d = k.createImageData(w, h);
      const e = canvas(w, h),
        ek = e.getContext('2d'),
        ed = ek.createImageData(w, h);
      for (let y = 0; y < h; y++)
        for (let x = 0; x < w; x++) {
          const gx = b.x0 + x,
            gy = b.y0 + y;
          if (lab(gx, gy) !== id) continue;
          const t = (y * w + x) * 4;
          ed.data[t + 3] = 255;
          d.data[t + 3] = md[mi(gx, gy) * 4 + 2];
        }
      // Локон = слой «до» под маской волос; рисуем без чтения пикселей с холста
      k.putImageData(d, 0, 0);
      k.globalCompositeOperation = 'source-in';
      k.drawImage(locksImg, -b.x0, -b.y0, IW, IH);
      k.globalCompositeOperation = 'source-over';
      ek.putImageData(ed, 0, 0);
      const p = {
        id,
        x: b.x0,
        y: b.y0,
        w,
        h,
        c,
        e,
        area: b.n,
        cut: false
      };
      pieces.push(p);
      byId.set(id, p);
      total += b.n;
    }
  }
  const labelAt = (x, y) => x < 0 || y < 0 || x >= IW || y >= IH ? 0 : labels[(y * MH / IH | 0) * MW + (x * MW / IW | 0)];

  // Срезанный локон: вырезаем из слоя и отправляем падать отдельной картинкой
  function drop(p) {
    if (p.cut) return;
    p.cut = true;
    cutArea += p.area;
    lctx.globalCompositeOperation = 'destination-out';
    lctx.drawImage(p.e, p.x, p.y);
    lctx.globalCompositeOperation = 'source-over';
    if (!reduce.matches) {
      const cx = p.x + p.w / 2,
        cy = p.y + p.h / 2;
      falling.push({
        p,
        x: cx,
        y: cy,
        vx: (Math.random() - .5) * 2.2 + (cx - IW / 2) * .006,
        vy: -1 - Math.random() * 2.5,
        rot: 0,
        vr: (Math.random() - .5) * .09,
        a: 1
      });
    }
  }

  // Проход курсором/пальцем: всё, чего коснулись по пути, отпадает целиком
  function snip(ax, ay, bx, by) {
    const dist = Math.hypot(bx - ax, by - ay),
      steps = Math.max(1, Math.ceil(dist / (R * .5)));
    let hit = false;
    for (let s = 0; s <= steps; s++) {
      const x = ax + (bx - ax) * s / steps,
        y = ay + (by - ay) * s / steps;
      for (const [dx, dy] of [
          [0, 0],
          [R, 0],
          [-R, 0],
          [0, R],
          [0, -R]
        ]) {
        const p = byId.get(labelAt(x + dx | 0, y + dy | 0));
        if (p && !p.cut) {
          drop(p);
          hit = true;
        }
      }
    }
    if (hit) {
      box.classList.add('is-started');
      progress();
      wake();
    }
  }

  // Прогресс по площади; с 90% оставшиеся локоны осыпаются сами и показывается финал
  function progress() {
    const p = cutArea / total;
    bar.style.width = (p * 100).toFixed(1) + '%';
    if (p >= .9 && !finishing) {
      finishing = true;
      const rest = pieces.filter(q => !q.cut).sort((a, b) => a.y - b.y);
      rest.forEach((q, i) => setTimeout(() => {
        drop(q);
        bar.style.width = (cutArea / total * 100).toFixed(1) + '%';
        wake();
      }, reduce.matches ? 0 : i * 40));
      setTimeout(() => {
        fadeTo = 0;
        if (reduce.matches) layerA = 0;
        wake();
        box.classList.add('is-done');
        done.hidden = false;
      }, reduce.matches ? 0 : rest.length * 40 + 500);
    }
  }

  // Отрисовка: итоговый вид, целые волосы одним слоем, падающие локоны, кольцо под пальцем
  function draw() {
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.fillStyle = bg;
    ctx.fillRect(0, 0, cv.width, cv.height);
    ctx.setTransform(dpr * scale, 0, 0, dpr * scale, dpr * ox, dpr * oy);
    ctx.drawImage(after, 0, 0, IW, IH);
    if (layerA > 0) {
      ctx.globalAlpha = layerA;
      ctx.drawImage(layer, 0, 0);
      ctx.globalAlpha = 1;
    }
    for (const f of falling) {
      ctx.save();
      ctx.globalAlpha = f.a;
      ctx.translate(f.x, f.y);
      ctx.rotate(f.rot);
      ctx.drawImage(f.p.c, -f.p.w / 2, -f.p.h / 2);
      ctx.restore();
    }
    for (const p of pointers.values())
      if (p.touch) {
        ctx.strokeStyle = 'rgba(194,165,106,.85)';
        ctx.lineWidth = 2 / scale;
        ctx.beginPath();
        ctx.arc(p.x, p.y, R * 1.2, 0, 7);
        ctx.stroke();
      }
  }

  // Анимация: падение локонов, отрастание при «Ещё раз», исчезновение слоя в финале
  function tick() {
    let busy = false;
    if (layerA !== fadeTo) {
      layerA = fadeTo > layerA ? Math.min(fadeTo, layerA + .06) : Math.max(fadeTo, layerA - .06);
      busy = true;
    }
    for (let i = falling.length - 1; i >= 0; i--) {
      const f = falling[i];
      f.vy += .45;
      f.x += f.vx;
      f.y += f.vy;
      f.rot += f.vr;
      f.a -= .014;
      if (f.a <= 0 || f.y - f.p.h > IH) falling.splice(i, 1);
    }
    draw();
    if (busy || falling.length || [...pointers.values()].some(p => p.touch)) requestAnimationFrame(tick);
    else running = false;
  }
  const wake = () => {
    if (!running && after) {
      running = true;
      requestAnimationFrame(tick);
    }
  };
  const toLocal = e => {
    const r = cv.getBoundingClientRect();
    return [(e.clientX - r.left - ox) / scale, (e.clientY - r.top - oy) / scale];
  };
  cv.addEventListener('pointerdown', e => {
    if (!labels) return;
    const [x, y] = toLocal(e);
    pointers.set(e.pointerId, {
      x,
      y,
      touch: e.pointerType !== 'mouse'
    });
    if (e.pointerType !== 'mouse') try {
      cv.setPointerCapture(e.pointerId);
    } catch {}
    if (!finishing) snip(x, y, x, y);
    wake();
  });
  cv.addEventListener('pointermove', e => {
    if (!labels) return;
    const [x, y] = toLocal(e), p = pointers.get(e.pointerId);
    if (!p) {
      if (e.pointerType === 'mouse') pointers.set(e.pointerId, {
        x,
        y,
        touch: false
      });
      return;
    }
    if (!finishing) snip(p.x, p.y, x, y);
    p.x = x;
    p.y = y;
    if (p.touch) wake();
  });
  const lift = e => {
    pointers.delete(e.pointerId);
    wake();
  };
  cv.addEventListener('pointerup', e => {
    if (e.pointerType !== 'mouse') lift(e);
  });
  cv.addEventListener('pointercancel', lift);
  cv.addEventListener('pointerleave', lift);
  again.addEventListener('click', () => {
    for (const p of pieces) p.cut = false;
    lctx.globalCompositeOperation = 'copy';
    lctx.drawImage(locksImg, 0, 0, IW, IH);
    lctx.globalCompositeOperation = 'source-over';
    fadeTo = 1;
    layerA = reduce.matches ? 1 : 0;
    falling.length = 0;
    cutArea = 0;
    finishing = false;
    box.classList.remove('is-done', 'is-started');
    done.hidden = true;
    bar.style.width = '0';
    wake();
  });

  // Размер холста по контейнеру с учётом плотности пикселей; картинка прижата к низу
  function fit() {
    const r = box.getBoundingClientRect();
    dpr = Math.min(2, window.devicePixelRatio || 1);
    cv.width = Math.round(r.width * dpr);
    cv.height = Math.round(r.height * dpr);
    scale = Math.min(r.width / IW, r.height / IH);
    ox = (r.width - IW * scale) / 2;
    oy = r.height - IH * scale;
    draw();
  }
  // Загрузка: фон рамки берём из угла картинки, чтобы не было стыка
  Promise.all([load(SRC.after), load(SRC.locks), readMap(SRC.map)]).then(([a, l, m]) => {
    after = a;
    IW = a.naturalWidth;
    IH = a.naturalHeight;
    R = IW * .022;
    const c = canvas(1, 1).getContext('2d');
    c.drawImage(a, 2, 2, 1, 1, 0, 0, 1, 1);
    const px = c.getImageData(0, 0, 1, 1).data;
    bg = `rgb(${px[0]},${px[1]},${px[2]})`;
    box.style.backgroundColor = bg;
    locksImg = l;
    layer = canvas(IW, IH);
    lctx = layer.getContext('2d');
    lctx.drawImage(l, 0, 0, IW, IH);
    build(l, m);
    box.classList.add('is-ready');
    new ResizeObserver(fit).observe(box);
    fit();
  }).catch(() => box.classList.add('is-failed'));
})();
