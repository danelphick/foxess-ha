const WORK_MODES = {
  ForceCharge:    { label: 'Force Charge',    color: '#2196F3' },
  ForceDischarge: { label: 'Force Discharge', color: '#FF5722' },
  Feedin:         { label: 'Feed In',         color: '#4CAF50' },
  SelfUse:        { label: 'Self Use',        color: '#9C27B0' },
  Backup:         { label: 'Backup',          color: '#FF9800' },
};

class FoxESSSchedulerCard extends HTMLElement {
  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._dialog = null;
    this._editGroups = null;
    this._deviceSN = null;
    this._drag = null;
    this._zoom = 1.0;
    this._tlScrollLeft = 0;
    this._edgeScrollId = null;
  }

  set hass(hass) {
    this._hass = hass;
    this._render();
  }

  setConfig(config) {
    this._config = config || {};
  }

  getCardSize() { return 5; }

  _findEntities() {
    const states = this._hass.states;
    let schedulerEnabled = null;
    let groupsEntityId = null;

    for (const [id, state] of Object.entries(states)) {
      if (!id.startsWith('sensor.')) continue;
      const attrs = state.attributes;
      if (Array.isArray(attrs.groups)) {
        groupsEntityId = id;
        this._deviceSN = attrs.device_sn ?? null;
      } else if (
        (state.state === 'enabled' || state.state === 'disabled') &&
        attrs.friendly_name?.toLowerCase().includes('scheduler')
      ) {
        schedulerEnabled = id;
      }
    }

    return { schedulerEnabled, groupsEntityId };
  }

  _toMins(timeStr) {
    if (!timeStr) return -1;
    const [h, m] = timeStr.split(':').map(Number);
    return h * 60 + m;
  }

  _minsToStr(mins) {
    return `${String(Math.floor(mins / 60)).padStart(2, '0')}:${String(mins % 60).padStart(2, '0')}`;
  }

  _render() {
    if (!this._hass) return;
    if (this._dialog?.open) return;

    const { schedulerEnabled, groupsEntityId } = this._findEntities();
    if (!schedulerEnabled && !groupsEntityId) {
      this.shadowRoot.innerHTML = `<ha-card><div style="padding:16px;color:var(--secondary-text-color)">No FoxESS scheduler entities found.</div></ha-card>`;
      return;
    }

    const now = new Date();
    const curMins = now.getHours() * 60 + now.getMinutes();
    const enabledState = schedulerEnabled ? (this._hass.states[schedulerEnabled]?.state ?? 'unavailable') : 'unavailable';

    const rawGroups = groupsEntityId ? (this._hass.states[groupsEntityId]?.attributes?.groups ?? []) : [];
    const slotData = rawGroups.map((g, idx) => {
      const startMins = g.startHour * 60 + g.startMinute;
      const endMins = g.endHour * 60 + g.endMinute;
      const isActive = !!g.enable && endMins > startMins &&
        curMins >= startMins && curMins < endMins;
      return {
        idx: idx + 1,
        state: g.workMode,
        start: `${String(g.startHour).padStart(2, '0')}:${String(g.startMinute).padStart(2, '0')}`,
        end: `${String(g.endHour).padStart(2, '0')}:${String(g.endMinute).padStart(2, '0')}`,
        enabled: !!g.enable,
        min_soc_on_grid: g.extraParam.minSocOnGrid,
        fd_soc:          g.extraParam.fdSoc,
        fd_pwr_w:        g.extraParam.fdPwr,
        max_soc:         g.extraParam.maxSoc ?? 100,
        startMins, endMins, isActive,
        cfg: WORK_MODES[g.workMode] ?? null,
      };
    }).filter(s => s.startMins !== s.endMins);

    const isRemaining = s => s.startMins === 0 && s.endMins === 1439;
    const remainingSlot = slotData.find(isRemaining) ?? null;
    const normalSlots = slotData.filter(s => !isRemaining(s));

    const toSeg = s => {
      const l = (s.startMins / 1440 * 100).toFixed(2);
      const w = ((s.endMins - s.startMins) / 1440 * 100).toFixed(2);
      return `<div class="seg${s.isActive ? ' seg-active' : ''}" data-slot="${s.idx}" style="left:${l}%;width:${w}%;background:${s.cfg.color}" title="${s.cfg.label}: ${s.start}–${s.end}"></div>`;
    };
    const segments = normalSlots
      .filter(s => s.enabled && s.cfg && s.startMins >= 0 && s.endMins > s.startMins)
      .map(toSeg).join('');

    const nowPct = (curMins / 1440 * 100).toFixed(2);

    const makeRow = (s, showTime) => {
      const color = (!s.enabled) ? '#9e9e9e' : (s.cfg?.color ?? '#9e9e9e');
      const modeLabel = s.cfg ? s.cfg.label : s.state;
      const badge = `<span class="badge" style="background:${color}33;border-color:${color}88">${modeLabel}</span>`;
      const pwr = s.fd_pwr_w != null ? (s.fd_pwr_w / 1000).toFixed(1) + ' kW' : '—';
      const timeCells = showTime
        ? `<td>${s.start ?? '—'}</td><td>${s.end ?? '—'}</td>`
        : `<td colspan="2" style="color:var(--secondary-text-color,#888)">Remaining Time Slots</td>`;
      return `<tr data-slot="${s.idx}" class="${s.isActive ? 'row-active' : ''} ${!s.enabled ? 'row-off' : ''}">
        ${timeCells}
        <td>${badge}</td>
        <td>${s.min_soc_on_grid ?? '—'}%</td>
        <td>${s.fd_soc ?? '—'}%</td>
        <td>${pwr}</td>
      </tr>`;
    };
    const normalRows = normalSlots.map(s => makeRow(s, true)).join('');
    const remainingRow = remainingSlot
      ? `<tr><td colspan="6" class="remaining-sep"></td></tr>${makeRow(remainingSlot, false)}`
      : '';
    const rows = normalRows + remainingRow;

    const statusCls = enabledState === 'enabled' ? 'status-on' : 'status-off';

    this.shadowRoot.innerHTML = `
      <style>
        ha-card { padding: 16px 16px 12px; }
        .hdr { display:flex; align-items:center; justify-content:space-between; margin-bottom:14px; }
        .hdr-right { display:flex; align-items:center; gap:8px; }
        .title { font-size:1.1em; font-weight:500; color:var(--primary-text-color); }
        .status { font-size:.75em; font-weight:600; padding:2px 10px; border-radius:12px; text-transform:capitalize; border:1px solid; }
        .status-on  { background:#4caf5033; border-color:#4caf5099; }
        .status-off { background:#9e9e9e33; border-color:#9e9e9e99; }
        .toggle-btn { cursor:pointer; font-family:inherit; }
        .toggle-btn:hover:not(:disabled) { filter:brightness(0.88); }
        .toggle-btn:disabled { cursor:wait; opacity:.6; }
        .edit-btn { font-size:.75em; padding:2px 10px; border-radius:12px; border:1px solid var(--primary-color,#03a9f4); background:transparent; cursor:pointer; }
        .edit-btn:hover { background:color-mix(in srgb,var(--primary-color,#03a9f4) 15%,transparent); }
        .tl { position:relative; height:24px; background:var(--divider-color,#e0e0e0); border-radius:5px; overflow:visible; margin-bottom:3px; }
        .seg { position:absolute; height:100%; border-radius:4px; opacity:.75; cursor:pointer; box-shadow:inset 0 0 0 1px rgba(255,255,255,.4); }
        .seg-active { opacity:1; box-shadow:0 1px 5px rgba(0,0,0,.3),inset 0 0 0 1px rgba(255,255,255,.4); }
        .seg.hovered { opacity:1; box-shadow:0 1px 8px rgba(0,0,0,.45),inset 0 0 0 1px rgba(255,255,255,.4); outline:2px solid rgba(255,255,255,.6); }
        .now { position:absolute; width:2px; height:32px; top:-4px; z-index:5; background:var(--primary-text-color,#333); border-radius:1px; pointer-events:none; }
        .tl-labels { display:flex; justify-content:space-between; font-size:.65em; color:var(--secondary-text-color); margin-bottom:12px; padding:0 1px; }
        table { width:100%; border-collapse:collapse; font-size:.82em; }
        th { padding:4px 5px; text-align:left; color:var(--secondary-text-color); font-weight:500; border-bottom:1px solid var(--divider-color); white-space:nowrap; }
        td { padding:5px 5px; color:var(--primary-text-color); white-space:nowrap; }
        .row-active td { background:rgba(3,169,244,.07); }
        .row-off td { color:var(--disabled-text-color,#aaa); }
        tr[data-slot] { cursor:pointer; }
        tr.hovered td { background:rgba(3,169,244,.15) !important; }
        .badge { font-size:.85em; padding:1px 8px; border-radius:10px; border:1px solid; }
        .remaining-sep { padding:5px 0 1px; border-top:1px solid var(--divider-color); }
      </style>
      <ha-card>
        <div class="hdr">
          <span class="title">FoxESS Scheduler</span>
          <div class="hdr-right">
            <button class="edit-btn" title="Edit schedule">Edit</button>
            <button class="status toggle-btn ${statusCls}" title="Toggle scheduler on/off">${enabledState}</button>
          </div>
        </div>
        <div class="tl">
          ${segments}
          <div class="now" style="left:${nowPct}%"></div>
        </div>
        <div class="tl-labels">
          <span>00:00</span><span>06:00</span><span>12:00</span><span>18:00</span><span>24:00</span>
        </div>
        <table>
          <thead><tr><th>Start</th><th>End</th><th>Mode</th><th>Min SoC</th><th>FD SoC</th><th>FD Power</th></tr></thead>
          <tbody>${rows}</tbody>
        </table>
      </ha-card>`;

    const root = this.shadowRoot;
    root.querySelectorAll('[data-slot]').forEach(el => {
      el.addEventListener('mouseenter', () => {
        root.querySelectorAll(`[data-slot="${el.dataset.slot}"]`).forEach(e => e.classList.add('hovered'));
      });
      el.addEventListener('mouseleave', () => {
        root.querySelectorAll(`[data-slot="${el.dataset.slot}"]`).forEach(e => e.classList.remove('hovered'));
      });
    });

    root.querySelector('.edit-btn')?.addEventListener('click', () => {
      this._openEditModal(slotData);
    });

    root.querySelector('.toggle-btn')?.addEventListener('click', async (e) => {
      if (!this._deviceSN) return;
      const btn = e.currentTarget;
      btn.disabled = true;
      const newEnable = enabledState === 'enabled' ? 0 : 1;
      try {
        await this._hass.connection.sendMessagePromise({
          type: 'foxess/set_scheduler_flag',
          deviceSN: this._deviceSN,
          enable: newEnable,
        });
      } catch (_err) {
        btn.disabled = false;
      }
    });
  }

  // ── Modal open ────────────────────────────────────────────────────────────

  _openEditModal(slotData) {
    this._zoom = 1.0;
    this._tlScrollLeft = 0;
    this._editGroups = slotData.map(s => ({
      startMins: s.startMins,
      endMins: s.endMins,
      enable: s.enabled ? 1 : 0,
      workMode: s.state,
      minSocOnGrid: s.min_soc_on_grid ?? 10,
      fdSoc: s.fd_soc ?? 90,
      fdPwr: s.fd_pwr_w ?? 0,
      maxSoc: s.max_soc ?? 100,
    }));

    if (!this._dialog || !this._dialog.isConnected) {
      this._dialog = document.createElement('dialog');
      this.shadowRoot.appendChild(this._dialog);
    }
    this._renderModal();
    this._dialog.showModal();
  }

  // ── Zoom helpers ──────────────────────────────────────────────────────────

  _getHourStep(zoom) {
    return zoom >= 6 ? 1 : zoom >= 3 ? 2 : zoom >= 1.5 ? 3 : 6;
  }

  _makeLabelHtml(zoom) {
    const hourStep = this._getHourStep(zoom);
    const items = [];
    for (let h = 0; h <= 24; h += hourStep) {
      const pct = (h / 24 * 100).toFixed(3);
      const xform = h === 0 ? '' : h === 24 ? 'transform:translateX(-100%)' : 'transform:translateX(-50%)';
      items.push(`<span style="position:absolute;left:${pct}%;white-space:nowrap;${xform}">${String(h).padStart(2, '0')}:00</span>`);
    }
    return items.join('');
  }

  _updateTlLabels() {
    const labelsInner = this._dialog?.querySelector('.tl-labels-inner');
    if (labelsInner) labelsInner.innerHTML = this._makeLabelHtml(this._zoom);
  }

  _applyZoom(factor, focalClientX, tlEl) {
    const rect = tlEl.getBoundingClientRect();
    const oldEffW = rect.width * this._zoom;
    const focalOff = focalClientX - rect.left + tlEl.scrollLeft;
    const oldStep = this._getHourStep(this._zoom);

    this._zoom = Math.max(1, Math.min(8, this._zoom * factor));

    const innerEl = tlEl.querySelector('.edit-tl-inner');
    if (innerEl) innerEl.style.width = `${this._zoom * 100}%`;

    const labelsOuter = this._dialog?.querySelector('.tl-labels-outer');
    const labelsInner = labelsOuter?.querySelector('.tl-labels-inner');
    if (labelsInner) labelsInner.style.width = `${this._zoom * 100}%`;

    const newEffW = rect.width * this._zoom;
    const newScroll = Math.max(0, Math.min(
      newEffW - rect.width,
      (focalOff / oldEffW) * newEffW - (focalClientX - rect.left)
    ));
    tlEl.scrollLeft = newScroll;
    this._tlScrollLeft = newScroll;
    if (labelsOuter) labelsOuter.scrollLeft = newScroll;

    if (this._getHourStep(this._zoom) !== oldStep) this._updateTlLabels();
  }

  // ── Modal render ──────────────────────────────────────────────────────────

  _renderModal() {
    if (!this._dialog) return;
    const groups = this._editGroups;
    const isRemaining = g => g.startMins === 0 && g.endMins === 1439;

    const segHtml = groups.map((g, idx) => {
      if (isRemaining(g)) return '';
      const cfg = WORK_MODES[g.workMode] ?? { color: '#9e9e9e' };
      const l = (g.startMins / 1440 * 100).toFixed(3);
      const w = ((g.endMins - g.startMins) / 1440 * 100).toFixed(3);
      const hatchDiv = g.enable ? '' : '<div class="hatch-overlay"></div>';
      return `<div class="seg-group" data-idx="${idx}" style="left:calc(${l}% - 12px);width:calc(${w}% + 24px)">
          <div class="edit-seg" data-idx="${idx}" style="background-color:${cfg.color}">${hatchDiv}</div>
          <div class="edge-handle lh" data-edge="left" data-idx="${idx}"></div>
          <div class="edge-handle rh" data-edge="right" data-idx="${idx}"></div>
        </div>`;
    }).join('');

    const makeEditRow = (g, idx, showTime) => {
      const cfg = WORK_MODES[g.workMode] ?? { color: '#9e9e9e' };
      const modeOpts = Object.entries(WORK_MODES).map(([k, { label }]) =>
        `<option value="${k}"${k === g.workMode ? ' selected' : ''}>${label}</option>`
      ).join('');
      const timeCells = showTime
        ? `<td class="time-start">${this._minsToStr(g.startMins)}</td><td class="time-end">${this._minsToStr(g.endMins)}</td>`
        : `<td colspan="2" style="color:var(--secondary-text-color,#888)">Remaining Time Slots</td>`;
      const delCell = showTime
        ? `<td><button class="del-btn" data-idx="${idx}" title="Delete"><ha-icon icon="mdi:delete"></ha-icon></button></td>`
        : `<td></td>`;
      return `<tr data-idx="${idx}">
        ${timeCells}
        <td><select class="mode-sel" data-idx="${idx}" style="border-left:3px solid ${cfg.color}">${modeOpts}</select></td>
        <td><input type="number" class="num-input" data-idx="${idx}" data-field="minSocOnGrid" value="${g.minSocOnGrid}" min="0" max="100" step="1" style="width:3.5em"></td>
        <td><input type="number" class="num-input" data-idx="${idx}" data-field="fdSoc" value="${g.fdSoc}" min="0" max="100" step="1" style="width:3.5em"></td>
        <td><input type="number" class="num-input" data-idx="${idx}" data-field="fdPwr" value="${g.fdPwr}" min="0" max="15000" step="100" style="width:4.5em"></td>
        <td style="text-align:center"><input type="checkbox" class="enable-cb" data-idx="${idx}"${g.enable ? ' checked' : ''}></td>
        ${delCell}
      </tr>`;
    };

    const normalRowHtml = groups.map((g, idx) => isRemaining(g) ? '' : makeEditRow(g, idx, true)).join('');
    const remainingIdx = groups.findIndex(isRemaining);
    const remainingRowHtml = remainingIdx >= 0
      ? `<tr><td colspan="8" class="remaining-sep"></td></tr>${makeEditRow(groups[remainingIdx], remainingIdx, false)}`
      : '';
    const rowHtml = normalRowHtml + remainingRowHtml;

    this._dialog.innerHTML = `
      <style>
        dialog {
          padding: 0; border: none; border-radius: 10px;
          background: var(--card-background-color, #fff);
          color: var(--primary-text-color, #333);
          box-shadow: 0 8px 32px rgba(0,0,0,.4);
          min-width: min(96vw, 600px); max-width: 96vw; max-height: 90vh;
          overflow-y: auto;
        }
        dialog::backdrop { background: rgba(0,0,0,.5); }
        .dlg-inner { padding: 16px; }
        .dlg-hdr { display:flex; align-items:center; justify-content:space-between; margin-bottom:14px; }
        .dlg-title { font-size:1.1em; font-weight:600; color:var(--primary-text-color,#333); }
        .close-btn { background:none; border:none; cursor:pointer; font-size:1.5em; line-height:1; padding:0 4px; color:var(--secondary-text-color,#888); }
        .close-btn:hover { color:var(--primary-text-color,#333); }
        .edit-tl {
          position: relative; height: 32px;
          background: var(--divider-color, #e0e0e0);
          border-radius: 5px; margin-bottom: 0;
          user-select: none; cursor: crosshair;
          overflow: hidden;
          touch-action: none;
          scrollbar-width: none;
        }
        .edit-tl::-webkit-scrollbar { display: none; }
        .edit-tl-inner { position: relative; height: 100%; min-width: 100%; }
        .tl-labels-outer {
          overflow: hidden; scrollbar-width: none;
          height: 20px; margin-bottom: 6px;
        }
        .tl-labels-outer::-webkit-scrollbar { display: none; }
        .tl-labels-inner {
          position: relative; height: 100%; min-width: 100%;
          font-size: .65em; color: var(--secondary-text-color);
        }
        .seg-group { position: absolute; height: 100%; overflow: visible; pointer-events: none; }
        .edit-seg {
          position: absolute; inset: 0 12px; border-radius: 3px;
          box-sizing: border-box; cursor: grab; overflow: hidden;
          opacity: .75; box-shadow: inset 0 0 0 1px rgba(255,255,255,.4);
          pointer-events: auto; touch-action: none;
        }
        .dlg-inner.seg-dragging, .dlg-inner.seg-dragging * { cursor: grabbing !important; }
        .dlg-inner.tl-panning, .dlg-inner.tl-panning * { cursor: grabbing !important; }
        .tl-labels-outer { cursor: grab; }
        .hatch-overlay {
          position: absolute; inset: 1px; pointer-events: none;
          background-image: repeating-linear-gradient(45deg,rgba(0,0,0,.18) 0,rgba(0,0,0,.18) 2px,transparent 2px,transparent 8px),
                            repeating-linear-gradient(135deg,rgba(0,0,0,.18) 0,rgba(0,0,0,.18) 2px,transparent 2px,transparent 8px);
          background-attachment: fixed;
        }
        .edge-handle {
          position: absolute; top: 0; width: 10px; height: 100%;
          cursor: col-resize; background: rgba(255,255,255,.4); z-index: 2;
          border-radius: 3px; transition: background .1s;
          display: none; pointer-events: auto; touch-action: none;
        }
        .edge-handle:hover { background: rgba(255,255,255,.75); }
        .edge-handle.h-visible { display: block; }
        .edge-handle.lh { left: 2px; transform: translateX(-2px); }
        .edge-handle.rh { right: 2px; transform: translateX(2px); }
        .edge-handle::before, .edge-handle::after {
          content: ''; position: absolute; top: 20%; height: 60%;
          width: 1px; border-radius: 1px; background: rgba(255,255,255,.7);
        }
        .edge-handle::before { left: 3px; }
        .edge-handle::after  { left: 6px; }
        .edit-seg.seg-hover { opacity:1; outline: 2px solid rgba(255,255,255,.6); box-shadow: 0 1px 8px rgba(0,0,0,.45),inset 0 0 0 1px rgba(255,255,255,.4); z-index: 1; }
        .table-wrap { overflow-x: auto; }
        .modal-table { width:100%; border-collapse:collapse; font-size:.82em; }
        .modal-table th { padding:3px 5px; text-align:left; color:var(--secondary-text-color,#888); font-weight:500; border-bottom:1px solid var(--divider-color,#e0e0e0); white-space:nowrap; }
        .modal-table td { padding:4px 5px; white-space:nowrap; color:var(--primary-text-color,#333); }
        select, input[type=number] {
          background: var(--secondary-background-color, #f5f5f5);
          color: inherit; border: 1px solid var(--divider-color,#ccc);
          border-radius: 4px; padding: 2px 4px; font-size: inherit;
          box-sizing: border-box;
        }
        input[type=number]::-webkit-inner-spin-button,
        input[type=number]::-webkit-outer-spin-button { -webkit-appearance: none; margin: 0; }
        input[type=number] { -moz-appearance: textfield; appearance: textfield; }
        input[type=checkbox] { cursor: pointer; width: 16px; height: 16px; accent-color: var(--primary-color,#03a9f4); }
        .mode-picker {
          position: fixed;
          background: var(--card-background-color, #fff);
          border: 1px solid var(--divider-color, #ccc);
          border-radius: 6px; box-shadow: 0 4px 16px rgba(0,0,0,.3);
          z-index: 10000; overflow: hidden; min-width: 140px;
        }
        .mode-picker button {
          display: block; width: 100%; padding: 7px 12px 7px 14px;
          border: none; background: none; cursor: pointer;
          text-align: left; font-size: .9em;
          color: var(--primary-text-color, #333);
          border-bottom: 1px solid var(--divider-color, #eee);
        }
        .mode-picker button:last-child { border-bottom: none; }
        .mode-picker button:hover { background: var(--secondary-background-color, #f0f0f0); }
        .mode-picker-sep { border-top: 1px solid var(--divider-color, #eee); margin: 2px 0 0; }
        .mode-picker .picker-del-btn { display: flex; align-items: center; justify-content: center; gap: 6px; color: var(--error-color, #f44336); border-left: none; }
        .mode-picker .picker-del-btn:hover { background: rgba(244,67,54,.1); }
        .dlg-footer { margin-top: 14px; }
        .modal-error { display: block; min-height: 1.3em; color: var(--error-color, #cf6679); font-size: .85em; margin-bottom: 6px; }
        .btn-row { display: flex; justify-content: flex-end; gap: 8px; align-items: center; }
        .action-btn { padding: 7px 20px; border-radius: 6px; border: none; cursor: pointer; font-size: .9em; font-weight: 500; }
        .save-btn { background-color: var(--primary-color, #03a9f4); background-image: linear-gradient(rgba(0,0,0,.2), rgba(0,0,0,.2)); color: #fff; }
        .save-btn:disabled { opacity: .5; cursor: default; }
        .cancel-btn { background: var(--secondary-background-color, #f0f0f0); color: var(--primary-text-color, #333); }
        .spinner { font-size: .85em; color: var(--secondary-text-color, #888); }
        .remaining-sep { padding:5px 0 1px; border-top:1px solid var(--divider-color,#e0e0e0); }
        .del-btn { background:none; border:none; cursor:pointer; padding:2px 4px; color:var(--error-color,#f44336); opacity:.6; border-radius:4px; display:flex; align-items:center; }
        .del-btn:hover { opacity:1; background:rgba(244,67,54,.1); }
      </style>
      <div class="dlg-inner">
        <div class="dlg-hdr">
          <span class="dlg-title">Edit Schedule</span>
          <button class="close-btn" aria-label="Close">&#x2715;</button>
        </div>
        <div class="edit-tl">
          <div class="edit-tl-inner" style="width:${this._zoom * 100}%;min-width:100%">
            ${segHtml}
          </div>
        </div>
        <div class="tl-labels-outer">
          <div class="tl-labels-inner" style="width:${this._zoom * 100}%;min-width:100%">
            ${this._makeLabelHtml(this._zoom)}
          </div>
        </div>
        <div class="table-wrap">
          <table class="modal-table">
            <thead><tr>
              <th>Start</th><th>End</th><th>Mode</th>
              <th>Min SoC%</th><th>FD SoC%</th><th>FD Pwr (W)</th><th style="text-align:center">On</th><th></th>
            </tr></thead>
            <tbody>${rowHtml}</tbody>
          </table>
        </div>
        <div class="dlg-footer">
          <span class="modal-error"></span>
          <div class="btn-row">
            <button class="action-btn cancel-btn">Cancel</button>
            <button class="action-btn save-btn">Save</button>
            <span class="spinner" style="display:none">Saving…</span>
          </div>
        </div>
      </div>`;

    this._attachModalListeners();

    // Restore scroll position after re-render
    const tl = this._dialog.querySelector('.edit-tl');
    const labelsOuter = this._dialog.querySelector('.tl-labels-outer');
    if (tl && this._tlScrollLeft > 0) {
      tl.scrollLeft = this._tlScrollLeft;
      if (labelsOuter) labelsOuter.scrollLeft = this._tlScrollLeft;
    }
  }

  _attachModalListeners() {
    const dlg = this._dialog;

    dlg.querySelector('.close-btn').addEventListener('click', () => dlg.close());
    dlg.querySelector('.cancel-btn').addEventListener('click', () => dlg.close());
    dlg.querySelector('.save-btn').addEventListener('click', () => this._saveSchedule());

    let hoverIdx = null;
    let bgTouchState = null;
    let pinchState = null;

    const showGroup = idx => {
      if (hoverIdx !== null && hoverIdx !== idx) hideGroup(hoverIdx);
      hoverIdx = idx;
      const grp = dlg.querySelector(`.seg-group[data-idx="${idx}"]`);
      if (grp) grp.style.zIndex = '1';
      dlg.querySelectorAll(`.edge-handle[data-idx="${idx}"]`).forEach(h => h.classList.add('h-visible'));
      dlg.querySelector(`.edit-seg[data-idx="${idx}"]`)?.classList.add('seg-hover');
    };
    const hideGroup = idx => {
      if (hoverIdx === idx) hoverIdx = null;
      const grp = dlg.querySelector(`.seg-group[data-idx="${idx}"]`);
      if (grp) grp.style.zIndex = '';
      dlg.querySelectorAll(`.edge-handle[data-idx="${idx}"]`).forEach(h => h.classList.remove('h-visible'));
      dlg.querySelector(`.edit-seg[data-idx="${idx}"]`)?.classList.remove('seg-hover');
    };

    dlg.querySelectorAll('.edit-seg').forEach(el => {
      el.addEventListener('mouseenter', e => {
        const newIdx = e.currentTarget.dataset.idx;
        // Suppress if cursor is still within the active group's bounds (adjacent seg-groups overlap by 24px)
        if (hoverIdx !== null && hoverIdx !== newIdx) {
          const activeGrp = dlg.querySelector(`.seg-group[data-idx="${hoverIdx}"]`);
          if (activeGrp) {
            const r = activeGrp.getBoundingClientRect();
            if (e.clientX >= r.left && e.clientX <= r.right &&
                e.clientY >= r.top && e.clientY <= r.bottom) return;
          }
        }
        showGroup(newIdx);
      });
      el.addEventListener('pointerdown', e => this._onSegBodyDown(e));
      el.addEventListener('dblclick', e => this._onSegDblClick(e));
      el.addEventListener('contextmenu', e => e.preventDefault());
    });

    const tl = dlg.querySelector('.edit-tl');

    // Background touch: long-press to create segment, swipe to pan when zoomed
    const clearBgTouch = pointerId => {
      if (bgTouchState?.pointerId === pointerId) {
        clearTimeout(bgTouchState.lpTimer);
        bgTouchState = null;
        dlg.querySelector('.dlg-inner')?.classList.remove('tl-panning');
      }
    };

    tl.addEventListener('pointerdown', e => {
      if (this._drag || bgTouchState) return;
      if (e.target.closest('.edit-seg, .edge-handle')) return;
      if (e.pointerType === 'mouse') {
        e.preventDefault();
        bgTouchState = {
          pointerId: e.pointerId,
          startX: e.clientX,
          startScrollLeft: tl.scrollLeft,
          moved: false,
          lpTimer: null,
        };
        tl.setPointerCapture(e.pointerId);
        return;
      }
      if (e.pointerType !== 'touch') return;
      const capturedClientX = e.clientX;
      bgTouchState = {
        pointerId: e.pointerId,
        startX: capturedClientX,
        startScrollLeft: tl.scrollLeft,
        moved: false,
        lpTimer: setTimeout(() => {
          bgTouchState = null;
          this._createSegmentAt(tl, capturedClientX);
        }, 500),
      };
      tl.setPointerCapture(e.pointerId);
    });

    tl.addEventListener('pointermove', e => {
      // Handle background pan (touch or mouse)
      if (bgTouchState && e.pointerId === bgTouchState.pointerId) {
        const dx = e.clientX - bgTouchState.startX;
        if (!bgTouchState.moved && Math.abs(dx) > 8) {
          clearTimeout(bgTouchState.lpTimer);
          bgTouchState.moved = true;
          dlg.querySelector('.dlg-inner')?.classList.add('tl-panning');
        }
        if (bgTouchState.moved && this._zoom > 1) {
          tl.scrollLeft = Math.max(0, bgTouchState.startScrollLeft - dx);
          this._tlScrollLeft = tl.scrollLeft;
          const labelsOuter = this._dialog?.querySelector('.tl-labels-outer');
          if (labelsOuter) labelsOuter.scrollLeft = tl.scrollLeft;
        }
        return;
      }

      // Existing hover management
      if (hoverIdx === null || this._drag) return;
      const grp = dlg.querySelector(`.seg-group[data-idx="${hoverIdx}"]`);
      if (!grp) return;
      const r = grp.getBoundingClientRect();
      if (e.clientX < r.left || e.clientX > r.right || e.clientY < r.top || e.clientY > r.bottom) {
        hideGroup(hoverIdx);
        // mouseenter won't re-fire if cursor was already inside the adjacent segment — show it explicitly
        const seg = e.target.closest('.edit-seg');
        if (seg) showGroup(seg.dataset.idx);
      }
    });

    tl.addEventListener('pointerup',     e => clearBgTouch(e.pointerId));
    tl.addEventListener('pointercancel', e => clearBgTouch(e.pointerId));

    tl.addEventListener('scroll', () => {
      this._tlScrollLeft = tl.scrollLeft;
      const labelsOuter = this._dialog?.querySelector('.tl-labels-outer');
      if (labelsOuter) labelsOuter.scrollLeft = tl.scrollLeft;
    });

    // Mouse pan on labels area
    const labelsOuter = dlg.querySelector('.tl-labels-outer');
    if (labelsOuter) {
      let labelsPanState = null;
      labelsOuter.addEventListener('pointerdown', e => {
        if (e.pointerType !== 'mouse' || labelsPanState) return;
        e.preventDefault();
        labelsPanState = { pointerId: e.pointerId, startX: e.clientX, startScrollLeft: tl.scrollLeft, moved: false };
        labelsOuter.setPointerCapture(e.pointerId);
      });
      labelsOuter.addEventListener('pointermove', e => {
        if (!labelsPanState || e.pointerId !== labelsPanState.pointerId) return;
        const dx = e.clientX - labelsPanState.startX;
        if (!labelsPanState.moved && Math.abs(dx) > 4) {
          labelsPanState.moved = true;
          dlg.querySelector('.dlg-inner')?.classList.add('tl-panning');
        }
        if (labelsPanState.moved && this._zoom > 1) {
          tl.scrollLeft = Math.max(0, labelsPanState.startScrollLeft - dx);
          this._tlScrollLeft = tl.scrollLeft;
          labelsOuter.scrollLeft = tl.scrollLeft;
        }
      });
      const clearLabels = e => {
        if (labelsPanState?.pointerId === e.pointerId) {
          labelsPanState = null;
          dlg.querySelector('.dlg-inner')?.classList.remove('tl-panning');
        }
      };
      labelsOuter.addEventListener('pointerup',     clearLabels);
      labelsOuter.addEventListener('pointercancel', clearLabels);
    }

    // Mouse wheel zoom
    tl.addEventListener('wheel', e => {
      e.preventDefault();
      this._applyZoom(e.deltaY < 0 ? 1.15 : 1 / 1.15, e.clientX, tl);
    }, { passive: false });

    // Pinch zoom via touch events
    const pinchData = touches => {
      const t1 = touches[0], t2 = touches[1];
      return {
        dist: Math.hypot(t1.clientX - t2.clientX, t1.clientY - t2.clientY),
        midX: (t1.clientX + t2.clientX) / 2,
      };
    };

    tl.addEventListener('touchstart', e => {
      if (e.touches.length !== 2) return;
      e.preventDefault();
      if (this._drag) {
        clearTimeout(this._drag.lpTimer);
        this._drag.el?.removeEventListener('pointermove', this._onSegBodyMove);
        this._drag.el?.removeEventListener('pointerup', this._onSegBodyUp);
        this._dialog.querySelector('.dlg-inner')?.classList.remove('seg-dragging');
        this._drag = null;
      }
      if (bgTouchState) { clearTimeout(bgTouchState.lpTimer); bgTouchState = null; }
      pinchState = pinchData(e.touches);
    }, { passive: false });

    tl.addEventListener('touchmove', e => {
      if (!pinchState || e.touches.length < 2) return;
      e.preventDefault();
      const cur = pinchData(e.touches);
      this._applyZoom(cur.dist / pinchState.dist, cur.midX, tl);
      pinchState = cur;
    }, { passive: false });

    tl.addEventListener('touchend', e => {
      if (e.touches.length < 2) pinchState = null;
    });

    tl.addEventListener('contextmenu', e => e.preventDefault());

    const withinActiveGroup = (clientX, clientY) => {
      if (hoverIdx === null) return false;
      const grp = dlg.querySelector(`.seg-group[data-idx="${hoverIdx}"]`);
      if (!grp) return false;
      const r = grp.getBoundingClientRect();
      return clientX >= r.left && clientX <= r.right &&
             (clientY === undefined || (clientY >= r.top && clientY <= r.bottom));
    };

    tl.addEventListener('mouseleave', e => {
      if (hoverIdx === null || this._drag) return;
      // Don't hide if cursor is still within the active seg-group's bounds
      // (handles protrude past the timeline's left/right edge)
      if (withinActiveGroup(e.clientX, e.clientY)) return;
      hideGroup(hoverIdx);
    });

    dlg.querySelectorAll('.edge-handle').forEach(el => {
      el.addEventListener('pointerdown', e => this._onEdgeDragStart(e));
      el.addEventListener('dblclick', e => e.stopPropagation());
      el.addEventListener('mouseleave', e => {
        if (hoverIdx === null || this._drag) return;
        if (!withinActiveGroup(e.clientX, e.clientY)) hideGroup(hoverIdx);
      });
    });

    tl.addEventListener('dblclick', e => this._onTlDblClick(e));

    dlg.querySelectorAll('.mode-sel').forEach(sel => {
      sel.addEventListener('change', e => {
        const idx = parseInt(e.currentTarget.dataset.idx);
        const mode = e.currentTarget.value;
        this._editGroups[idx].workMode = mode;
        const cfg = WORK_MODES[mode] ?? { color: '#9e9e9e' };
        const segEl = dlg.querySelector(`.edit-seg[data-idx="${idx}"]`);
        if (segEl) this._applySegBg(segEl, cfg.color, this._editGroups[idx].enable);
        e.currentTarget.style.borderLeftColor = cfg.color;
      });
    });

    dlg.querySelectorAll('.num-input').forEach(inp => {
      inp.addEventListener('change', e => {
        const idx = parseInt(e.currentTarget.dataset.idx);
        const field = e.currentTarget.dataset.field;
        this._editGroups[idx][field] = parseInt(e.currentTarget.value) || 0;
      });
    });

    dlg.querySelectorAll('.enable-cb').forEach(cb => {
      cb.addEventListener('change', e => {
        const idx = parseInt(e.currentTarget.dataset.idx);
        this._editGroups[idx].enable = e.currentTarget.checked ? 1 : 0;
        const segEl = dlg.querySelector(`.edit-seg[data-idx="${idx}"]`);
        if (segEl) {
          const cfg = WORK_MODES[this._editGroups[idx].workMode] ?? { color: '#9e9e9e' };
          this._applySegBg(segEl, cfg.color, this._editGroups[idx].enable);
        }
      });
    });

    dlg.querySelectorAll('.del-btn').forEach(btn => {
      btn.addEventListener('click', e => {
        const idx = parseInt(e.currentTarget.dataset.idx);
        this._editGroups.splice(idx, 1);
        this._renderModal();
      });
    });
  }

  _applySegBg(el, color, enable) {
    el.style.backgroundColor = color;
    let overlay = el.querySelector('.hatch-overlay');
    if (!enable) {
      if (!overlay) {
        overlay = document.createElement('div');
        overlay.className = 'hatch-overlay';
        el.appendChild(overlay);
      }
    } else {
      overlay?.remove();
    }
  }

  // ── Drag logic ────────────────────────────────────────────────────────────

  _onEdgeDragStart(e) {
    e.preventDefault();
    e.stopPropagation();
    const handle = e.currentTarget;
    const groupIdx = parseInt(handle.dataset.idx);
    const edge = handle.dataset.edge;

    const tl = this._dialog.querySelector('.edit-tl');
    const tlRect = tl.getBoundingClientRect();
    const groups = this._editGroups;
    const g = groups[groupIdx];

    // Find immediately adjacent (touching) group
    let adjacentIdx = null;
    if (edge === 'left') {
      for (let i = 0; i < groups.length; i++) {
        if (i !== groupIdx && groups[i].endMins === g.startMins) { adjacentIdx = i; break; }
      }
    } else {
      for (let i = 0; i < groups.length; i++) {
        if (i !== groupIdx && groups[i].startMins === g.endMins) { adjacentIdx = i; break; }
      }
    }

    // Precompute bounds that don't depend on shift state
    let noShiftBound;
    if (edge === 'left') {
      noShiftBound = groups.reduce((mx, gr, i) =>
        i !== groupIdx && gr.endMins <= g.startMins ? Math.max(mx, gr.endMins) : mx, 0);
    } else {
      const nexts = groups
        .filter((gr, i) => i !== groupIdx && gr.startMins >= g.endMins)
        .map(gr => gr.startMins);
      noShiftBound = nexts.length ? Math.min(...nexts) : 1440;
    }

    // Shift bound: adjacent must keep ≥10 min duration
    const shiftBound = adjacentIdx !== null
      ? (edge === 'left'
          ? groups[adjacentIdx].startMins + 10
          : groups[adjacentIdx].endMins - 10)
      : (edge === 'left' ? 0 : 1440);

    this._drag = { groupIdx, edge, adjacentIdx, noShiftBound, shiftBound, lastClientX: e.clientX, lastShiftKey: e.shiftKey };
    handle.setPointerCapture(e.pointerId);
    handle.addEventListener('pointermove', this._onEdgeDragMove);
    handle.addEventListener('pointerup', this._onEdgeDragEnd);
    this._startEdgeScrollLoop();
  }

  _onEdgeDragMove = (e) => {
    if (!this._drag) return;
    this._drag.lastClientX = e.clientX;
    this._drag.lastShiftKey = e.shiftKey;
    this._applyEdgeDragPos(e.clientX, e.shiftKey);
  }

  _onEdgeDragEnd = (e) => {
    if (!this._drag) return;
    this._stopEdgeScrollLoop();
    const handle = e.currentTarget;
    handle.releasePointerCapture(e.pointerId);
    handle.removeEventListener('pointermove', this._onEdgeDragMove);
    handle.removeEventListener('pointerup', this._onEdgeDragEnd);
    this._drag = null;
    this._renderModal();
  }

  // ── Segment body drag (move) ──────────────────────────────────────────────

  _onSegBodyDown(e) {
    if (e.pointerType === 'mouse' && e.button !== 0) return;
    if (this._drag) return;
    e.stopPropagation();
    const el = e.currentTarget;
    const groupIdx = parseInt(el.dataset.idx);
    const pointerId = e.pointerId;
    const lpTimer = setTimeout(() => {
      if (this._drag?.type !== 'move-pending') return;
      el.removeEventListener('pointermove', this._onSegBodyMove);
      el.removeEventListener('pointerup', this._onSegBodyUp);
      try { el.releasePointerCapture(pointerId); } catch (_) {}
      this._drag = null;
      this._showModePicker(el, groupIdx);
    }, 500);
    this._drag = { type: 'move-pending', groupIdx, startX: e.clientX, el, lpTimer };
    el.setPointerCapture(e.pointerId);
    el.addEventListener('pointermove', this._onSegBodyMove);
    el.addEventListener('pointerup', this._onSegBodyUp);
  }

  _onSegBodyMove = (e) => {
    if (!this._drag) return;
    if (this._drag.type === 'move-pending') {
      if (Math.abs(e.clientX - this._drag.startX) < 5) return;
      clearTimeout(this._drag.lpTimer);
      this._activateSegMoveDrag(e);
      // fall through to process the first move frame
    }
    if (this._drag.type !== 'move') return;
    this._drag.lastClientX = e.clientX;
    this._drag.lastShiftKey = e.shiftKey;
    this._applySegMoveDragPos(e.clientX, e.shiftKey);
  }

  _onSegBodyUp = (e) => {
    if (!this._drag) return;
    clearTimeout(this._drag.lpTimer);
    this._stopEdgeScrollLoop();
    const { el } = this._drag;
    el.releasePointerCapture(e.pointerId);
    el.removeEventListener('pointermove', this._onSegBodyMove);
    el.removeEventListener('pointerup', this._onSegBodyUp);
    const wasActive = this._drag.type === 'move';
    this._drag = null;
    this._dialog.querySelector('.dlg-inner')?.classList.remove('seg-dragging');
    if (wasActive) this._renderModal();
  }

  _activateSegMoveDrag(e) {
    const { groupIdx, startX } = this._drag;
    const groups = this._editGroups;
    const g = groups[groupIdx];
    const tl = this._dialog.querySelector('.edit-tl');
    const tlRect = tl.getBoundingClientRect();
    const effW = tlRect.width * this._zoom;
    const duration = g.endMins - g.startMins;

    // Offset: where in the segment the pointer was at pointerdown (unrounded)
    const mouseOffsetMins = ((startX - tlRect.left + tl.scrollLeft) / effW) * 1440 - g.startMins;

    let leftAdjIdx = null, rightAdjIdx = null;
    for (let i = 0; i < groups.length; i++) {
      if (i === groupIdx) continue;
      if (groups[i].endMins === g.startMins) leftAdjIdx = i;
      if (groups[i].startMins === g.endMins) rightAdjIdx = i;
    }

    // No-shift bounds: the gap the segment currently occupies
    const noShiftMinStart = groups.reduce((mx, gr, i) =>
      i !== groupIdx && gr.endMins <= g.startMins ? Math.max(mx, gr.endMins) : mx, 0);
    const noShiftRightEdge = groups.reduce((mn, gr, i) =>
      i !== groupIdx && gr.startMins >= g.endMins ? Math.min(mn, gr.startMins) : mn, 1440);
    const noShiftMaxStart = noShiftRightEdge - duration;

    // Shift bounds: adjacent keeps ≥10 min
    const shiftMinStart = leftAdjIdx !== null ? groups[leftAdjIdx].startMins + 10 : noShiftMinStart;
    const shiftMaxEnd   = rightAdjIdx !== null ? groups[rightAdjIdx].endMins - 10 : noShiftRightEdge;
    const shiftMaxStart = shiftMaxEnd - duration;

    Object.assign(this._drag, {
      type: 'move',
      duration, mouseOffsetMins,
      leftAdjIdx, rightAdjIdx,
      noShiftMinStart, noShiftMaxStart,
      shiftMinStart, shiftMaxStart,
      lastClientX: e.clientX,
      lastShiftKey: e.shiftKey,
    });
    this._dialog.querySelector('.dlg-inner')?.classList.add('seg-dragging');
    this._startEdgeScrollLoop();
  }

  _applyEdgeDragPos(clientX, shiftKey) {
    const { groupIdx, edge, adjacentIdx, noShiftBound, shiftBound } = this._drag;
    const groups = this._editGroups;
    const g = groups[groupIdx];
    const tl = this._dialog.querySelector('.edit-tl');
    const tlRect = tl.getBoundingClientRect();
    const rawMins = Math.round(((clientX - tlRect.left + tl.scrollLeft) / (tlRect.width * this._zoom)) * 1440 / 10) * 10;
    const useShift = shiftKey && adjacentIdx !== null;
    const bound = useShift ? shiftBound : noShiftBound;
    let newMins;
    if (edge === 'left') {
      newMins = Math.max(bound, Math.min(g.endMins - 10, rawMins));
      if (useShift) { groups[adjacentIdx].endMins = newMins; this._updateSegStyle(adjacentIdx); this._updateTableRowTimes(adjacentIdx); }
      g.startMins = newMins;
    } else {
      newMins = Math.min(bound, Math.max(g.startMins + 10, rawMins));
      if (useShift) { groups[adjacentIdx].startMins = newMins; this._updateSegStyle(adjacentIdx); this._updateTableRowTimes(adjacentIdx); }
      g.endMins = newMins;
    }
    this._updateSegStyle(groupIdx);
    this._updateTableRowTimes(groupIdx);
  }

  _applySegMoveDragPos(clientX, shiftKey) {
    const { groupIdx, duration, mouseOffsetMins,
            leftAdjIdx, rightAdjIdx,
            noShiftMinStart, noShiftMaxStart, shiftMinStart, shiftMaxStart } = this._drag;
    const groups = this._editGroups;
    const g = groups[groupIdx];
    const tl = this._dialog.querySelector('.edit-tl');
    const tlRect = tl.getBoundingClientRect();
    const rawMins = ((clientX - tlRect.left + tl.scrollLeft) / (tlRect.width * this._zoom)) * 1440;
    const newStart = Math.max(
      shiftKey ? shiftMinStart : noShiftMinStart,
      Math.min(shiftKey ? shiftMaxStart : noShiftMaxStart, Math.round((rawMins - mouseOffsetMins) / 10) * 10)
    );
    const newEnd = newStart + duration;
    g.startMins = newStart;
    g.endMins = newEnd;
    this._updateSegStyle(groupIdx);
    this._updateTableRowTimes(groupIdx);
    if (shiftKey) {
      if (leftAdjIdx !== null) { groups[leftAdjIdx].endMins = newStart; this._updateSegStyle(leftAdjIdx); this._updateTableRowTimes(leftAdjIdx); }
      if (rightAdjIdx !== null) { groups[rightAdjIdx].startMins = newEnd; this._updateSegStyle(rightAdjIdx); this._updateTableRowTimes(rightAdjIdx); }
    }
  }

  _startEdgeScrollLoop() {
    if (this._edgeScrollId !== null) return;
    const ZONE = 50;
    const tick = () => {
      if (!this._drag) { this._edgeScrollId = null; return; }
      const tl = this._dialog?.querySelector('.edit-tl');
      if (!tl) { this._edgeScrollId = null; return; }

      const { lastClientX, lastShiftKey } = this._drag;
      const tlRect = tl.getBoundingClientRect();
      const distLeft  = lastClientX - tlRect.left;
      const distRight = tlRect.right - lastClientX;

      let scrollDelta = 0;
      if (distLeft  < ZONE) scrollDelta = -(1 - Math.max(0, distLeft)  / ZONE) * 8;
      else if (distRight < ZONE) scrollDelta =  (1 - Math.max(0, distRight) / ZONE) * 8;

      if (scrollDelta !== 0) {
        const maxScroll = tl.scrollWidth - tl.clientWidth;
        if (maxScroll > 0) {
          const newScroll = Math.max(0, Math.min(maxScroll, tl.scrollLeft + scrollDelta));
          if (Math.abs(newScroll - tl.scrollLeft) >= 0.5) {
            tl.scrollLeft = newScroll;
            this._tlScrollLeft = newScroll;
            const lo = this._dialog?.querySelector('.tl-labels-outer');
            if (lo) lo.scrollLeft = newScroll;
            if (this._drag.edge !== undefined) this._applyEdgeDragPos(lastClientX, lastShiftKey ?? false);
            else if (this._drag.type === 'move') this._applySegMoveDragPos(lastClientX, lastShiftKey ?? false);
          }
        }
      }

      this._edgeScrollId = requestAnimationFrame(tick);
    };
    this._edgeScrollId = requestAnimationFrame(tick);
  }

  _stopEdgeScrollLoop() {
    if (this._edgeScrollId !== null) {
      cancelAnimationFrame(this._edgeScrollId);
      this._edgeScrollId = null;
    }
  }

  _updateSegStyle(idx) {
    const g = this._editGroups[idx];
    const el = this._dialog.querySelector(`.seg-group[data-idx="${idx}"]`);
    if (!el) return;
    el.style.left  = `calc(${(g.startMins / 1440 * 100).toFixed(3)}% - 12px)`;
    el.style.width = `calc(${((g.endMins - g.startMins) / 1440 * 100).toFixed(3)}% + 24px)`;
  }

  _updateTableRowTimes(idx) {
    const g = this._editGroups[idx];
    const row = this._dialog.querySelector(`tr[data-idx="${idx}"]`);
    if (!row) return;
    const sc = row.querySelector('.time-start');
    const ec = row.querySelector('.time-end');
    if (sc) sc.textContent = this._minsToStr(g.startMins);
    if (ec) ec.textContent = this._minsToStr(g.endMins);
  }

  // ── Mode picker ───────────────────────────────────────────────────────────

  _showModePicker(segEl, groupIdx) {
    this._dialog.querySelector('.mode-picker')?.remove();

    const picker = document.createElement('div');
    picker.className = 'mode-picker';
    picker.style.cssText = 'position:fixed;z-index:10000';

    const segRect = segEl.getBoundingClientRect();
    picker.style.left = segRect.left + 'px';
    picker.style.top  = (segRect.bottom + 4) + 'px';

    picker.innerHTML = Object.entries(WORK_MODES).map(([key, { label, color }]) =>
      `<button data-mode="${key}" style="border-left:4px solid ${color}">${label}</button>`
    ).join('') +
      `<div class="mode-picker-sep"></div>
       <button class="picker-del-btn"><ha-icon icon="mdi:delete"></ha-icon>Delete</button>`;

    this._dialog.appendChild(picker);

    picker.querySelectorAll('button[data-mode]').forEach(btn => {
      btn.addEventListener('click', ev => {
        ev.stopPropagation();
        this._editGroups[groupIdx].workMode = btn.dataset.mode;
        picker.remove();
        this._renderModal();
      });
    });

    picker.querySelector('.picker-del-btn').addEventListener('click', ev => {
      ev.stopPropagation();
      this._editGroups.splice(groupIdx, 1);
      picker.remove();
      this._renderModal();
    });

    // Dismiss on click/tap elsewhere
    setTimeout(() => {
      const dismiss = ev => {
        if (!picker.contains(ev.target)) {
          picker.remove();
          this._dialog.removeEventListener('click', dismiss);
          document.removeEventListener('click', dismiss);
        }
      };
      this._dialog.addEventListener('click', dismiss);
      document.addEventListener('click', dismiss);
    }, 0);
  }

  _onSegDblClick(e) {
    e.stopPropagation();
    this._showModePicker(e.currentTarget, parseInt(e.currentTarget.dataset.idx));
  }

  // ── Create segment ────────────────────────────────────────────────────────

  _createSegmentAt(tl, clientX) {
    const tlRect = tl.getBoundingClientRect();
    const clickMins = Math.round(
      ((clientX - tlRect.left + tl.scrollLeft) / (tlRect.width * this._zoom)) * 1440 / 10
    ) * 10;

    const groups = this._editGroups;
    const prevEnd   = groups.reduce((mx, g) => g.endMins   <= clickMins ? Math.max(mx, g.endMins)   : mx, 0);
    const nextStart = groups.reduce((mn, g) => g.startMins >  clickMins ? Math.min(mn, g.startMins) : mn, 1440);

    if (nextStart - prevEnd < 20) return;

    const startMins = Math.max(prevEnd, Math.min(clickMins, nextStart - 10));
    const endMins   = Math.min(startMins + 60, nextStart);

    groups.push({ startMins, endMins, enable: 1, workMode: 'SelfUse', minSocOnGrid: 10, fdSoc: 90, fdPwr: 0, maxSoc: 100 });
    groups.sort((a, b) => a.startMins - b.startMins);
    this._renderModal();
  }

  _onTlDblClick(e) {
    if (e.target !== e.currentTarget && e.target.closest?.('.edit-seg')) return;
    this._createSegmentAt(e.currentTarget, e.clientX);
  }

  // ── Save ──────────────────────────────────────────────────────────────────

  async _saveSchedule() {
    const dlg      = this._dialog;
    const saveBtn  = dlg.querySelector('.save-btn');
    const spinner  = dlg.querySelector('.spinner');
    const errEl    = dlg.querySelector('.modal-error');

    saveBtn.disabled     = true;
    spinner.style.display = 'inline';
    errEl.textContent    = '';

    const groups = this._editGroups.map(g => ({
      enable:       g.enable,
      startHour:    Math.floor(g.startMins / 60),
      startMinute:  g.startMins % 60,
      endHour:      Math.floor(g.endMins / 60),
      endMinute:    g.endMins % 60,
      workMode:     g.workMode,
      extraParam: {
        minSocOnGrid: g.minSocOnGrid,
        fdSoc:        g.fdSoc,
        fdPwr:        g.fdPwr,
        maxSoc:       g.maxSoc ?? 100,
      },
    }));

    try {
      await this._hass.connection.sendMessagePromise({
        type: 'foxess/save_schedule',
        deviceSN: this._deviceSN,
        groups,
      });
      dlg.close();
    } catch (err) {
      errEl.textContent = err.message || 'Save failed — please try again.';
    } finally {
      saveBtn.disabled     = false;
      spinner.style.display = 'none';
    }
  }
}

customElements.define('foxess-scheduler-card', FoxESSSchedulerCard);
window.customCards = window.customCards || [];
window.customCards.push({
  type: 'foxess-scheduler-card',
  name: 'FoxESS Scheduler',
  description: 'Displays the FoxESS inverter charge/discharge schedule with a 24-hour timeline.',
  preview: false,
});
